"""
Container API — creates connections that can be used to start the processes within the container.
"""

# -----------------------------------------------------------------------------
# Imports
# -----------------------------------------------------------------------------

# Local
from xhtml2statpub import convert
from config import logger

# In-built
import io, zipfile
import json
import os
import tempfile
import asyncio
import shutil
from typing import Optional
from pathlib import Path

# Pip installed
from fastapi import FastAPI, UploadFile
from fastapi.responses import Response

# -----------------------------------------------------------------------------
# FastAPI app
# -----------------------------------------------------------------------------

app = FastAPI(title="XHTML to Statpub")

# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------

BASE_DIR = Path(__file__).resolve().parent
STATIC_DIR = BASE_DIR / "static"

class Args:
    def __init__(self, **kwargs):
        for k, v in kwargs.items():
            setattr(self, k, v)
        self.logger = logger

def make_folders(tmp_root: Path) -> dict:
    folders = {
        "cwd":    str(BASE_DIR),
        "input":  str(tmp_root / "input"),
        "output": str(tmp_root / "output"),
        "logs":   str(tmp_root / "logs"),
        "static": str(STATIC_DIR),
        "tmp":    str(tmp_root / "tmp"),
        "source": str(tmp_root / "tmp" / "source"),
        "target": str(tmp_root / "tmp" / "target"),
        "root":   str(tmp_root / "tmp" / "target"),
        "epub":   str(tmp_root / "tmp" / "target"),
    }
    for key, p in folders.items():
        if key in ("static", "cwd"):
            continue
        Path(p).mkdir(parents=True, exist_ok=True)
    return folders

def to_bool(val):
    return str(val).lower() == "true"

def trinn_to_grade(trinn_list):
    mapping = {
        "Barnehage": 0, "1.kl": 1, "2.kl": 2, "3.kl": 3,
        "4.kl": 4, "5.kl": 5, "6.kl": 6, "7.kl": 7,
        "8.kl": 8, "9.kl": 9, "10.kl": 10,
        "Vg1": 11, "Vg2": 12, "Vg3": 13
    }
    grades = [mapping[t] for t in trinn_list if t in mapping]
    return max(grades) if grades else None

# -----------------------------------------------------------------------------
# API methods
# -----------------------------------------------------------------------------

current_job = {"status": "Idle", "step": None}

@app.get("/health")
async def health():
    """Returns health state of container."""
    return {"health": "ok"}

@app.post("/process")
async def process(file: UploadFile, config: UploadFile, file2: Optional[UploadFile] = None):
    """
    Receives files and config from controller, runs module processing,
    and returns results as a zip.

    Args:
        file: Primary .xhtml file to process.
        config: JSON config file with module parameters.
        file2: Unused.

    Returns:
        Response: Zip containing processed files and log.json.
    """
    module_name = os.getenv("MODULE_NAME", "unknown")
    logger.info(f"/process inside {module_name} started")

    try:
        # --- Staging area 1: Unpack ---
        config_data = json.loads(await config.read())
        file_bytes = await file.read()
        filename = file.filename

        tmp_root = Path(tempfile.mkdtemp())
        input_path = tmp_root / filename
        input_path.write_bytes(file_bytes)

        job_dir = tmp_root / "job_output"
        job_dir.mkdir()
        folders = make_folders(tmp_root)

        args = Args(
            input=str(input_path),
            folders=folders,
            production_number=Path(filename).stem,
            data=file_bytes,
            job_id=Path(filename).stem,
            job_dir=job_dir,
            grade=trinn_to_grade(config_data.get("trinn", [])),
            mathematics=to_bool(config_data.get("mathematics", False)),
            science=to_bool(config_data.get("science", False)),
            relocate=to_bool(config_data.get("relocate", True)),
            aggressive=to_bool(config_data.get("aggressive", False)),
            llm=to_bool(config_data.get("llm", False)),
            link_footnotes=False,   # P: inactive
            verbose=False,          # P: inactive
            toc_levels=None,        # P: inactive
            p_length=None,          # P: inactive
        )

        # --- Process ---
        return_code = await asyncio.to_thread(convert, args)
        log_records = [{
            "level": "INFO" if return_code and return_code.get("status") == "ok" else "ERROR",
            "message": f"convert() returned {return_code}",
            "timestamp": None
        }]
        report = None
        report_extension = None

        # --- Staging area 2: Pack zip ---
        module_version = os.getenv(f"{module_name.upper()}_VERSION", "unknown")
        log_records.insert(0, {
            "level": "INFO",
            "message": module_version,
            "timestamp": None
        })

        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w") as zf:
            for output_file in job_dir.rglob("*"):
                if output_file.is_file():
                    zf.write(output_file, output_file.relative_to(job_dir))
            if log_records:
                zf.writestr("log.json", json.dumps(log_records))
            if report:
                zf.writestr(f"report{report_extension or '.bin'}", report)
        buf.seek(0)

    finally:
        shutil.rmtree(tmp_root, ignore_errors=True)

    logger.info(f"/process inside {module_name} returns")
    return Response(
        content=buf.read(),
        media_type="application/zip",
        headers={"Content-Disposition": f'attachment; filename="{Path(filename).stem}.zip"'}
    )

@app.get("/status")
async def status():
    """Returns process status of container."""
    return current_job