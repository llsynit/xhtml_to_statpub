"""
Container configuration.
"""

import logging
import sys
from pathlib import Path
import os

def setup_logger():
    """
    Configures and returns the module-level logger.

    Outputs INFO-level logs to stdout in timestamped format.
    """
    module_log_level = os.getenv("MODULE_NAME", "unknown").upper() + "_LOG_LEVEL" # Pulls log level from .env
    level = int(os.getenv(module_log_level, logging.INFO))
    logging.basicConfig(
        level=level,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[logging.StreamHandler(sys.stdout)]
    )
    logging.getLogger("python_multipart.multipart").setLevel(logging.WARNING) # Supresses DEBUG prints from python-multipart
    return logging.getLogger(__name__)

logger = setup_logger()

BASE_DIR = Path(__file__).parent
ARTIFACTS_ROOT = (BASE_DIR / "artifacts").resolve()
ARTIFACTS_ROOT.mkdir(parents=True, exist_ok=True)

# P: imported by xhtml2statpub.py but unused in test-sm
MODULE_NAME_XHTML_TO_STATPUB = "xhtml2statpub"
PORT_XHTML_TO_STATPUB = 34505
RABBITMQ_URL = ""
WORK_EXCHANGE = ""
RESULTS_EXCHANGE = ""
WORK_ROUTING_KEY_XHTML_TO_STATPUB = ""
WORK_QUEUE_NAME_XHTML_TO_STATPUB = ""
ARTIFACTS_RETENTION_HOURS = 24
ARTIFACTS_CLEAN_INTERVAL_SEC = 3600
WORKER_BASE_URL_XHTML_TO_STATPUB = ""
WORKER_BASE_URL = ""