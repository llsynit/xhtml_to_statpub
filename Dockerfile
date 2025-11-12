# Bruk en slank base
FROM python:3.12-slim

# --- Miljøvariabler / paths ---
ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PIP_NO_CACHE_DIR=1 \
    HOME=/app \
    MPLCONFIGDIR=/app/.cache/matplotlib \
    NLTK_DATA=/usr/local/share/nltk_data

WORKDIR /app

# --- Systemavhengigheter ---
# tesseract-ocr: for pytesseract (OCR)
# default-jre-headless: for Java-baserte verktøy (f.eks. epubcheck / Saxon)
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      tesseract-ocr \
      default-jre-headless \
 && rm -rf /var/lib/apt/lists/*

# Kataloger som trenger å finnes og være skrivbare
RUN mkdir -p "$MPLCONFIGDIR" "$NLTK_DATA"

# --- Python-avhengigheter ---
COPY requirements.txt .
RUN python -m pip install --no-cache-dir -r requirements.txt

# Last ned NLTK-ressurser ved build (slipper nett-krav ved runtime)
RUN python - <<'PY'
import nltk
for pkg in ("punkt", "punkt_tab"):
    try:
        nltk.download(pkg)
    except Exception as e:
        print(f"WARN: download of {pkg} failed:", e)
PY

# --- App-kode ---
COPY saxon static app.py config.py utils.py xhtml2statpub.py app/
RUN mkdir -p /app/artifacts

# --- Non-root bruker ---
RUN useradd -m -u 10001 appuser \
 && chown -R appuser:appuser /app "$NLTK_DATA"

USER appuser

EXPOSE 39005
CMD ["uvicorn", "app:app", "--host", "0.0.0.0", "--port", "39005"]
