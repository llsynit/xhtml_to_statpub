from __future__ import annotations

import tempfile
import logging
from pathlib import Path
from types import SimpleNamespace
from typing import Optional

from bs4 import BeautifulSoup
from fastapi import FastAPI, File, Form, UploadFile
from fastapi.responses import Response

# Importér selve transformasjonen
from nlbpub2statpub import apply_requirements

app = FastAPI(title="nlbpub_to_statpub", version="1.0.0")

BASE_DIR = Path(__file__).resolve().parent
STATIC_DIR = BASE_DIR / "static"


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

    # Les fil og parse som XML/XHTML
    data = await file.read()
    try:
        soup = BeautifulSoup(data, "xml")
    except Exception:
        # fallback hvis 'xml'-parser ikke er tilgjengelig
        soup = BeautifulSoup(data, "lxml-xml")

    # Bygg args-objektet (dot-notasjon) slik apply_requirements forventer
    args = SimpleNamespace(
        mathematics=bool(mathematics),
        science=bool(science),
        grade=(int(grade) if grade is not None and str(grade).strip() != "" else None),
    )

    # Kjør transformasjonen
    soup = apply_requirements(soup, logger, folders, args)

    # Serialiser tilbake til XHTML
    xhtml = soup.prettify(formatter="minimal")
    return Response(content=xhtml.encode("utf-8"),
                    media_type="application/xhtml+xml; charset=utf-8")
