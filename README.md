# Statped Mark‑up Requirements Converter (XHTML → Statped XHTML)

This project converts XHTML produced from EPUBs that follow the **Nordic Guidelines** into XHTML that conforms to **Statped Mark‑up Requirements (SMR)**.  
It is designed to run both as a **CLI tool** and as a small **HTTP service** (FastAPI).

Target users are production pipelines adapting textbooks for students who are blind or visually impaired. The converter focuses on **semantic, screen‑reader‑friendly** markup and idempotent transformations.

---

## Repository layout

```
/Dockerfile
/app.py                # HTTP server (FastAPI)
/xhtml2statpub.py      # Main CLI converter (earlier: nlbpub2statpub.py)
/requirements.txt
/static/               # Optional static assets (css, etc.)
```

---

## Installation

### Local Python

```bash
python3.11 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

### Docker

```bash
docker build -t xhtml_to_statpub .
docker run --rm -p 9002:9002 xhtml_to_statpub
```

---

## Usage

### CLI

```bash
python xhtml2statpub.py input.xhtml -o output.xhtml -vv -m
```

### HTTP API

```bash
uvicorn app:app --host 0.0.0.0 --port 9002
```

Send file with curl:

```bash
curl -F "file=@input.xhtml" http://localhost:9002/run -o output.xhtml
```

---

## Command‑line arguments

- `-o, --output`: Output XHTML path  
- `--mathematics`: Enable math‑specific rules  
- `--toc-levels`: TOC depth  
- `--p-length`: Paragraph length threshold  
- `--link_footnotes`: Enable linking footnotes  
- `--relocate`: Enable relocation passes  
- `--llm`: Enable LLM assistance (optional)  
- `-v/-vv`: Verbosity

---

## SMR rules (high‑level)

- **2.1 General cleanup** (CSS, relocation, emphasis, NBSP, TOC normalization, etc.)  
- **2.2 Thematic grouping** (wrap headings in `<section>`, fix chapter sections)  
- **2.3 Images** (alt text, figure text extraction, prodnote asides)  
- **2.4 Lists** (non‑standard numbering, avoid `<p>` in `<li>`, description lists relocation, etc.)  
- **2.5 Tasks** (task headings, subordinate headings, match problems, fill‑in‑the‑blank, etc.)  

Many rules are placeholders with TODOs or LLM hooks for future expansion.

---

## Development notes

- Idempotent transformations: running converter twice should not change file further.  
- LLM support is optional (via RabbitMQ).  
- Logging is controlled by `-v`/`-vv` (CLI) or `LOG_LEVEL` (Docker).

---

## License

© Statped. Internal use project. License to be decided.
