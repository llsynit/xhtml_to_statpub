from __future__ import annotations
import os
import uuid
import tempfile
import logging
import time
from datetime import datetime

from pathlib import Path
from types import SimpleNamespace
from typing import Optional, Dict
from urllib.parse import urlparse
from contextlib import suppress
import asyncio
import aio_pika
import httpx
from bs4 import BeautifulSoup
from fastapi import FastAPI, File, Form, UploadFile, HTTPException
from fastapi.responses import Response
from fastapi.staticfiles import StaticFiles

from aiormq.exceptions import AMQPConnectionError
from dotenv import load_dotenv

from utils import summarize_artifacts, cleanup_artifacts_once

from config import (MODULE_NAME_XHTML_TO_STATPUB, PORT_XHTML_TO_STATPUB, RABBITMQ_URL,
                    WORK_EXCHANGE, RESULTS_EXCHANGE,
                    WORK_ROUTING_KEY_XHTML_TO_STATPUB, WORK_QUEUE_NAME_XHTML_TO_STATPUB,
                    ARTIFACTS_ROOT, ARTIFACTS_RETENTION_HOURS,
                    ARTIFACTS_CLEAN_INTERVAL_SEC,
                    WORKER_BASE_URL)

load_dotenv()
# Importér selve transformasjonen
from xhtml2statpub import convert


# -----------------------------------------------------------------------------
# Logger
# -----------------------------------------------------------------------------


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger(__name__)

logging.getLogger("aio_pika").setLevel(logging.WARNING)
logging.getLogger("aiormq").setLevel(logging.WARNING)


# =============================================================================
# FastAPI
# =============================================================================
logger.info(
    f"Starting {MODULE_NAME_XHTML_TO_STATPUB} on port {PORT_XHTML_TO_STATPUB}.....")

app = FastAPI(title=MODULE_NAME_XHTML_TO_STATPUB, version="1.0.0")

BASE_DIR = Path(__file__).resolve().parent
STATIC_DIR = BASE_DIR / "static"
DOWNLOADS: Dict[str, bytes] = {}
app.state.amqp_enabled = False
app.state.amqp_conn = None
app.state.amqp_ch = None
app.state._amqp_reconnector_task = None  # background task handle
RECONNECT_DELAY_SECONDS = 30

# Track current job to avoid deleting it while processing (optional but recommended)
app.state.current_job = getattr(app.state, "current_job", {
                                "running": False, "production_number": None, "status": None, "job_id": None})


# Serve ephemeral artifacts (no persistent volume!)
app.mount("/artifacts", StaticFiles(directory=str(ARTIFACTS_ROOT)),
          name="artifacts")

# =============================================================================
# Small helpers
# =============================================================================


async def _http_download_to(dst: Path, url: str):
    """Download http(s) or copy file:// to dst"""
    dst.parent.mkdir(parents=True, exist_ok=True)
    u = urlparse(url)
    if u.scheme in ("http", "https"):
        async with httpx.AsyncClient(timeout=120) as http:
            r = await http.get(url)
            r.raise_for_status()
            dst.write_bytes(r.content)
    elif u.scheme == "file":
        src = Path(u.path)
        if not src.exists():
            raise FileNotFoundError(f"file:// source not found: {src}")
        dst.write_bytes(src.read_bytes())
    else:
        raise HTTPException(400, f"Unsupported URI scheme: {u.scheme}")


def _art_uri(job_id: str,  name: str) -> str:
    return f"{WORKER_BASE_URL}/artifacts/{job_id}/{name}"


async def _publish_result(stage: str, job_id: str, status: str, artifacts: Dict, correlation_id: Optional[str]):
    rk = f"job.{job_id}.stage.{stage}.status.{status}"
    payload = {
        "job_id": job_id,
        "stage": stage,
        "status": status,          # "ok" | "fail"
        "artifacts": artifacts,    # URIs (ephemeral here)
        "finished_at": time.time()
    }
    body = __import__("json").dumps(
        payload, ensure_ascii=False).encode("utf-8")
    msg = aio_pika.Message(
        body=body,
        content_type="application/json",
        delivery_mode=aio_pika.DeliveryMode.PERSISTENT,
        correlation_id=correlation_id,
        message_id=str(uuid.uuid4()),
    )
    await app.state.results_ex.publish(msg, routing_key=rk)




def make_logger() -> logging.Logger:
    """Logger som skriver til stdout (synlig i docker logs)."""
    logger = logging.getLogger("nlbpub_to_statpub")
    if not logger.handlers:
        logger.setLevel(logging.INFO)
        h = logging.StreamHandler()
        h.setFormatter(logging.Formatter("[%(levelname)s] %(message)s"))
        logger.addHandler(h)
    return logger


def make_folders(tmp_root: Optional[Path] = None) -> dict:
    """
    Bygg mappestrukturen som apply_requirements() forventer.
    Vi lager en liten temp-tre slik at CSS-kopien o.l. kan gjennomføres.
    """
    root = Path(tempfile.mkdtemp(prefix="nlbpub2statpub-")) if tmp_root is None else tmp_root

    folders = {
        "cwd": str(BASE_DIR),
        "input": str(root / "input"),
        "output": str(root / "output"),
        "logs": str(root / "logs"),
        "static": str(STATIC_DIR),
        "tmp": str(root / "tmp"),
        "source": str(root / "tmp" / "source"),
        "target": str(root / "tmp" / "target"),
            "root": str(root / "tmp" / "target"),
        "epub": str(root / "tmp" / "target"),
    }
    # Sørg for at mappene eksisterer
    for key, p in folders.items():
        if key in ("static", "cwd"):
            continue
        Path(p).mkdir(parents=True, exist_ok=True)
    return folders


@app.get("/health")
def health():
    return {"status": "ok"}


@app.post("/run")
async def run(
    file: UploadFile = File(..., description="XHTML fra forrige steg i pipelinen"),
    # Felter som controlleren allerede sender (noen er ikke brukt her, men tillates for kompatibilitet):
    mathematics: bool = Form(False),
    science: bool = Form(False),
    grade: Optional[int] = Form(None),
    link_footnotes: bool = Form(False),  # ikke brukt her
    verbose: bool = Form(False),         # ikke brukt her
    toc_levels: Optional[int] = Form(None),  # ikke brukt her
    p_length: Optional[int] = Form(None),    # ikke brukt her
    relocate: bool = Form(True),
    llm: bool = Form(False),
):
    """
    Ta imot en XHTML-fil, kjør apply_requirements, og returnér bearbeidet XHTML.
    """
    logger = make_logger()
    folders = make_folders()
    production_number = Path(file).stem
    timestamp = datetime.now().strftime("%Y-%m-%d-%H%M%S%f")
    job_id = f"{production_number}-{timestamp}"
    job_dir = ARTIFACTS_ROOT / job_id
    logger.info(f"Job dir: {job_dir}")

    # MOVED TO xhtml_to_statpub.py
    '''
    # Les fil og parse som XML/XHTML
    data = await file.read()
    try:
        soup = BeautifulSoup(data, "xml")
    except Exception:
        # fallback hvis 'xml'-parser ikke er tilgjengelig
        soup = BeautifulSoup(data, "lxml-xml")
    '''

    # Bygg args-objektet (dot-notasjon) slik apply_requirements forventer
    args = SimpleNamespace(
        file=file,
        folders=folders,
        mathematics=bool(mathematics),
        science=bool(science),
        grade=(int(grade) if grade is not None and str(grade).strip() != "" else None),
    )

    # MOVED TO xhtml_to_statpub.py
    # Kjør transformasjonen
    # soup = apply_requirements(soup, logger, folders, args)

    # MOVED TO xhtml_to_statpub.py
    # Serialiser tilbake til XHTML
    # xhtml = soup.prettify(formatter="minimal")
    xhtml = convert(args, logger)
    return Response(content=xhtml.encode("utf-8"),
                    media_type="application/xhtml+xml; charset=utf-8")


# =============================================================================
# RabbitMQ consumer
# =============================================================================


async def _handle_work_message(m: aio_pika.IncomingMessage):
    async with m.process():
        data = __import__("json").loads(m.body.decode("utf-8"))
        inputs = data.get("inputs") or {}
        file =  inputs.get("xhtml_uri"),
        mathematics = data.get("job_id"),
        science = data.get("job_id"),
        grade = data.get("job_id"),
        link_footnotes = data.get("job_id"),  # ikke brukt her
        verbose = data.get("job_id"),         # ikke brukt her
        toc_levels =data.get("job_id"),  # ikke brukt her
        p_length = data.get("job_id"),    # ikke brukt her
        relocate = data.get("job_id"),
        llm = data.get("llm")
        stage = data.get("stage")
        job_id = data.get("job_id")
        corr_id = data.get("correlation_id") or m.correlation_id


        job_dir = ARTIFACTS_ROOT / job_id
        tmp_xhtml = job_dir / "input.xhtml"
         # 1) Fetch xhtml
        await _http_download_to(tmp_xhtml, file)

        # 2) Run insert_metadata
        try:
            status = insert_metadata(production_number, job_id, str(tmp_xhtml), str(
                tmp_opf), publication_format="epub")
        except Exception as e:
            # crash → publish fail
            artifacts = {"error": f"insert_metadata crashed: {e}"}
            await _publish_result(stage, job_id, "fail", artifacts, corr_id)
            try:
                tmp_xhtml.unlink(missing_ok=True)
            except Exception:
                pass
            return
        finally:
            try:
                tmp_opf.unlink(missing_ok=True)
            except Exception:
                pass

        if not os.path.isdir(job_dir):
            await _publish_result(stage, job_id, "fail",
                                  {"error": f"Could not find artifact folder for this job: {job_dir}"},
                                  corr_id)
            return
        artifacts = {}
        # Build artifact URIs (use relative names under job_dir)
        # Go through all content of job_dir and create URIs for them ignore images folder
        for path in job_dir.rglob("*"):
            if path.is_file() and "images" not in str(path):
                # use name of the file as key and add to artifacts dict
                artifacts[str(path.relative_to(job_dir))] = _art_uri(
                    job_id, str(path.relative_to(job_dir)))

        # Normalize status to "ok"/"fail"
        if isinstance(status, dict):
            status_value = status.get("status")
        else:
            status_value = "ok" if status else "fail"

        logger.info("Publishing result to controller...")
        logger.info(
            f"[{MODULE_NAME_XHTML_TO_STATPUB}] job {job_id} stage {stage} completed, status: {status_value}")
        await _publish_result(stage, job_id, status_value, artifacts, corr_id)


async def _amqp_reconnector_loop():
    """
    Optional: background loop to try reconnecting periodically.
    Never raises. Stops when app shuts down.
    """
    while True:
        if app.state.amqp_enabled:
            await asyncio.sleep(RECONNECT_DELAY_SECONDS)
            continue

        ok = await _setup_amqp_once()
        if ok:
            # Connected; loop keeps running in case it drops later.
            await asyncio.sleep(RECONNECT_DELAY_SECONDS)
        else:
            await asyncio.sleep(RECONNECT_DELAY_SECONDS)


async def _setup_amqp_once():
    try:
        # AMQP connect
        app.state.amqp_conn = await aio_pika.connect_robust(RABBITMQ_URL)
        ch = await app.state.amqp_conn.channel()
        await ch.set_qos(prefetch_count=1)
        app.state.amqp_ch = ch

        # Exchanges
        app.state.work_ex = await ch.declare_exchange(WORK_EXCHANGE, aio_pika.ExchangeType.DIRECT, durable=True)
        app.state.results_ex = await ch.declare_exchange(RESULTS_EXCHANGE, aio_pika.ExchangeType.TOPIC, durable=True)

        # Queue + bind
        q = await ch.declare_queue(WORK_QUEUE_NAME_XHTML_TO_STATPUB, durable=True)
        await q.bind(app.state.work_ex, routing_key=WORK_ROUTING_KEY_XHTML_TO_STATPUB)

        # Start consuming
        await q.consume(_handle_work_message)
        logger.info(
            f"[{MODULE_NAME_XHTML_TO_STATPUB}] consuming: exchange='{WORK_EXCHANGE}' rk='{WORK_ROUTING_KEY_XHTML_TO_STATPUB}' queue='{WORK_QUEUE_NAME_XHTML_TO_STATPUB}'")
        return True
    except (AMQPConnectionError, OSError, ConnectionRefusedError) as e:
        # Log as WARNING (not ERROR) so app continues running
        logger.warning(
            "[%s] AMQP connection failed (%s). Running without RabbitMQ. "
            "HTTP endpoints remain available.",
            MODULE_NAME_XHTML_TO_STATPUB, repr(e)
        )
        # Ensure disabled state
        app.state.amqp_enabled = False
        app.state.amqp_conn = None
        app.state.amqp_ch = None
        return False


async def _cleanup_loop():
    """
    Periodically clean up old artifacts. Never raises.
    """
    while True:
        try:
            stats = cleanup_artifacts_once(
                ARTIFACTS_ROOT, ARTIFACTS_RETENTION_HOURS, logger)
            logger.debug("Artifacts cleanup stats: %s", stats)
        except Exception as e:
            logger.warning("Artifacts cleanup loop error: %r", e)
        await asyncio.sleep(ARTIFACTS_CLEAN_INTERVAL_SEC)


@app.on_event("startup")
async def on_startup():
    # Try once, but do NOT crash the app if it fails
    ok = await _setup_amqp_once()
    if not ok:
        # Optionally, start a background reconnector
        app.state._amqp_reconnector_task = asyncio.create_task(
            _amqp_reconnector_loop())

    logger.info("Starting artifacts cleanup loop...")
    app.state._cleanup_task = asyncio.create_task(_cleanup_loop())


@app.on_event("shutdown")
async def shutdown():
    # stop cleanup loop
    task = getattr(app.state, "_cleanup_task", None)
    if task:
        task.cancel()
        with suppress(asyncio.CancelledError):
            await task

    # stop amqp reconnector loop (if it was started)
    task = getattr(app.state, "_amqp_reconnector_task", None)
    if task:
        task.cancel()
        with suppress(asyncio.CancelledError):
            await task

    # close AMQP channel/connection if present
    ch = getattr(app.state, "amqp_ch", None)
    if ch:
        with suppress(Exception):
            await ch.close()

    conn = getattr(app.state, "amqp_conn", None)
    if conn:
        with suppress(Exception):
            await conn.close()
