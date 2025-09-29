# Bruk en slank base
FROM python:3.12-slim

# --- Systemavhengigheter (juster etter behov) ---
# tesseract-ocr: trengs av pytesseract hvis du bruker OCR
# default-jre-headless: trengs hvis python-pakken epubcheck bruker Java
RUN apt-get update && apt-get install -y --no-install-recommends \
    tesseract-ocr \
    default-jre-headless \
 && rm -rf /var/lib/apt/lists/*

# --- Kataloger og miljø ---
WORKDIR /app

# Gjør cache/konfigskriving mulig for Matplotlib og NLTK
ENV HOME=/app \
    MPLCONFIGDIR=/app/.cache/matplotlib \
    NLTK_DATA=/usr/local/share/nltk_data \
    PIP_NO_CACHE_DIR=1

RUN mkdir -p "$MPLCONFIGDIR" "$NLTK_DATA"

# --- Avhengigheter ---
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Last ned NLTK-ressurser ved byggtid (ikke ved runtime)
# punkt_tab finnes i nyere NLTK (>=3.9)
RUN python - <<'PY'
import nltk
try:
    nltk.download('punkt')
except Exception as e:
    print("WARN: punkt download failed:", e)
try:
    nltk.download('punkt_tab')
except Exception as e:
    print("WARN: punkt_tab download failed (ok på eldre NLTK):", e)
PY

# --- App-kode ---
COPY . .

# (Valgfritt) kjør som non-root med skrivetilgang
RUN useradd -m -u 10001 appuser && chown -R appuser:appuser /app /usr/local/share/nltk_data
USER appuser

EXPOSE 9002
CMD ["uvicorn", "app:app", "--host", "0.0.0.0", "--port", "9002"]
