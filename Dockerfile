FROM python:3.12-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    MODULE_NAME=xhtml2statpub \
    PORT=34505 \
    APP_HOME=/app \
    MPLCONFIGDIR=/app/.cache/matplotlib \
    NLTK_DATA=/usr/local/share/nltk_data

WORKDIR ${APP_HOME}

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        tesseract-ocr \
        default-jre-headless \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p "$MPLCONFIGDIR" "$NLTK_DATA"

COPY requirements.txt ./requirements.txt
RUN pip install --no-cache-dir pip setuptools wheel \
    && pip install --no-cache-dir -r requirements.txt

RUN python - <<'PY'
import nltk
for pkg in ("punkt", "punkt_tab"):
    try:
        nltk.download(pkg)
    except Exception as e:
        print(f"WARN: download of {pkg} failed:", e)
PY

RUN useradd -u 1000 -ms /bin/bash appuser \
    && chown -R appuser:appuser /app "$NLTK_DATA"

COPY --chown=appuser:appuser . /app
RUN mkdir -p ${APP_HOME}/artifacts ${APP_HOME}/static

USER appuser

EXPOSE 34505
HEALTHCHECK --interval=20s --timeout=3s --retries=5 CMD python -c \
    "import socket; s=socket.create_connection(('127.0.0.1', 34505), 2); s.close()"

CMD ["uvicorn", "app:app", "--host", "0.0.0.0", "--port", "34505"]