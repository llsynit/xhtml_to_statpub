'''
This script converts an epub conforming to the
"Nordic Guidelines for the Production of Accessible EPUB 3" to an
epub conforming to the "Statped Mark-up Requirements" specification.

Discuss: should EPUB for Education Structural Semantics be
better integrated into the script? 
https://idpf.org/epub/profiles/edu/structure/
'''

# IMPORTS
# =======

import logging
from logging            import getLogger, DEBUG, INFO, WARNING, StreamHandler, Formatter
from argparse           import ArgumentParser
from bs4                import BeautifulSoup, NavigableString, Comment, Tag
from lxml               import etree
from io                 import StringIO, BytesIO
from glob               import glob
from zipfile            import ZipFile, ZIP_DEFLATED
from shutil             import rmtree, copytree, copyfile, make_archive, move
from os                 import path, mkdir, getcwd, walk, remove, rename, makedirs
from pathlib            import Path
from nltk.tokenize      import word_tokenize
from ipapy              import is_valid_ipa
from epubcheck          import EpubCheck
from unicodedata        import normalize
from pika               import BlockingConnection, ConnectionParameters, PlainCredentials
from time               import sleep, time
from collections        import Counter
from urllib.parse       import urlparse, unquote
from datetime           import datetime
from collections.abc    import Iterable
from typing import (
    Any,
    Optional,
    Iterable,
    Callable,
    Union,
    Tuple,
    Dict,
    List,
    Set,
)

import sys, unicodedata, string, re, nltk, subprocess, pytesseract #spacy, cv2, json, uuid

import xml.etree.ElementTree    as ET
import numpy                    as np
import pandas                   as pd
import matplotlib.pyplot        as plt
import csv

import nltk
try:
    nltk.data.find('tokenizers/punkt')
except LookupError:
    pass  # logg/ignorer, filene skal allerede være på plass fra Dockerfile
try:
    nltk.data.find('tokenizers/punkt_tab')
except LookupError:
    pass

try:
    from PIL import Image
except ImportError:
    import Image

from config import (MODULE_NAME_XHTML_TO_STATPUB, PORT_XHTML_TO_STATPUB, RABBITMQ_URL,
                    WORK_EXCHANGE, RESULTS_EXCHANGE,
                    WORK_ROUTING_KEY_XHTML_TO_STATPUB, WORK_QUEUE_NAME_XHTML_TO_STATPUB,
                    ARTIFACTS_ROOT, ARTIFACTS_RETENTION_HOURS,
                    ARTIFACTS_CLEAN_INTERVAL_SEC,
                    WORKER_BASE_URL_XHTML_TO_STATPUB)

# VARIBLES
# ========


xhtml_string = ' '.join([
    '<?xml version="1.0" encoding="UTF-8"?>',
    '<!DOCTYPE html>',
    '<html>',
    '<head>',
    '<meta charset="UTF-8"/>',
    '<meta content="863500" name="dc:identifier"/>',
    '<meta content="width=device-width" name="viewport"/>',
    '<link href="css/ebok.css" rel="stylesheet" type="text/css"/>',
    '</head>',
    '</html',])

correct_html_tag = ' '.join([
    'xmlns="http://www.w3.org/1999/xhtml"',
    'xmlns:xml="http://www.w3.org/XML/1998/namespace"',
    'xmlns:epub="http://www.idpf.org/2007/ops"',
    'epub:prefix="z3998: http://www.daisy.org/z3998/2012/vocab/structure/#"',
    ])

correct_package_tag = ' '.join([
    '<package',
    'xmlns="http://www.idpf.org/2007/opf"',
    'xmlns:dc="http://purl.org/dc/elements/1.1/"',
    'xmlns:epub="http://www.idpf.org/2007/ops"',
    'prefix="nordic: http://www.mtm.se/epub/"',
    'version="3.0"',
    'xml:lang="no"',
    'unique-identifier="pub-identifier"',
    '>'])

xslt_file = 'html-to-nav.xsl'

# CONSTANTS
# =========

BASE_DIR = Path(__file__).parent
ARTIFACTS_ROOT = (BASE_DIR / "artifacts").resolve()
ARTIFACTS_ROOT.mkdir(parents=True, exist_ok=True)

TMP_DIR     = path.join(path.dirname(path.abspath(__file__)), 'tmp')
#STATIC_DIR  = BASE_DIR #path.join(path.dirname(path.abspath(__file__)), 'static')
STATIC_DIR  = BASE_DIR / "static" 
OUTPUT_DIR  = path.join(path.dirname(path.abspath(__file__)), 'output')

PUNCTUATION = string.punctuation

SYMBOLS     = [
        '§',
        '$',
        '£',
        '€',
        '¥',
        ]

# https://idpf.org/epub/profiles/edu/structure/#h.ipobyxqoqtux
ASSESSMENTS = [
            'assessment',
            'assessments',
            'fill-in-the-blank-problem',
            'general-problem',
            'match-problem',
            'multiple-choice-problem',
            'practice',
            'practices',
            'qna',
            'true-false-problem']

NUMBERS = { # TODO: This list should be common to 2.4.1.2
            'no' : {
                'en'    : 1,
                'to'    : 2,
                'tre'   : 3,
                'fire'  : 4,
                'fem'   : 5,
                'seks'  : 6,
                'sju'   : 7,
                'åtte'  : 8,
                'ni'    : 9,
                'ti'    : 10},
            'nb' : {
                'en'    : 1,
                'to'    : 2,
                'tre'   : 3,
                'fire'  : 4,
                'fem'   : 5,
                'seks'  : 6,
                'sju'   : 7,
                'åtte'  : 8,
                'ni'    : 9,
                'ti'    : 10},
            'nn' : {
                'en'    : 1,
                'to'    : 2,
                'tre'   : 3,
                'fire'  : 4,
                'fem'   : 5,
                'seks'  : 6,
                'sju'   : 7,
                'åtte'  : 8,
                'ni'    : 9,
                'ti'    : 10},
            'en' : {
                'one'   : 1,
                'two'   : 2,
                'three' : 3,
                'four'  : 4,
                'five'  : 5,
                'six'   : 6,
                'seven' : 7,
                'eight' : 8,
                'nine'  : 9,
                'ten'   : 10},
            'de' : {
                'eins'  : 1,
                'zwei'  : 2,
                'drei'  : 3,
                'vier'  : 4,
                'fünf'  : 5,
                'sechs' : 6,
                'sieben': 7,
                'acht'  : 8,
                'neun'  : 9,
                'zehn'  : 10},
            'fr' : {
                'un'    : 1,
                'deux'  : 2,
                'trois' : 3,
                'quatre': 4,
                'cinq'  : 5,
                'six'   : 6,
                'sept'  : 7,
                'huit'  : 8,
                'neuf'  : 9,
                'dix'   : 10}
            }

BULLETS = ['•',
           '‣',
           '⁃',
           '⁌',
           '⁍',
           '∙',
           '○',
           '●',
           '◘',
           '◦',
           '☙',
           '❥',
           '❧',
           '⦾',
           '⦿',
           '-']

HEADINGS = {
        'en' : 'Glossary',
        'nn' : 'Ordforklaringar',
        'nb' : 'Ordforklaringer',
        'no' : 'Ordforklaringer'}

PAGES = {
        'da' : 'Side',
        'nl' : 'Bladzijde',
        'en' : 'Page',
        'fi' : 'Sivu',
        'fr' : 'Page',
        'is' : 'Síðu',
        'it' : 'Pagina',
        'la' : 'Pagina',
        'no' : 'Side',
        'nb' : 'Side',
        'nn' : 'Side',
        'sv' : 'Sida'}

BLOCK_ELEMENTS = [
        'address',
        'article',
        'aside',
        'blockquote',
        'canvas',
        'dd',
        'div',
        'dl',
        'dt',
        'fieldset',
        'figcaption',
        'figure',
        'footer',
        'form',
        'h1', 'h2', 'h3', 'h4', 'h5', 'h6',
        'header',
        'hr',
        'li',
        'main',
        'nav',
        'noscript',
        'ol',
        'p',
        'pre',
        'section',
        'table',
        'tfoot',
        'ul',
        'video']

# https://www.iana.org/assignments/language-subtag-registry/language-subtag-registry
# https://spacy.io/models
# These need to be installed with 'python -m spacy download <model>'
LANGUAGE_MODELS = {
    'ca' : 'ca_core_news_trf',          # 'ca_core_news_sm',
    'zh' : 'zh_core_web_trf',           # 'zh_core_web_sm',
    'hr' : 'hr_core_news_lg',           # 'hr_core_news_sm',
    'da' : 'da_core_news_trf',          # 'da_core_news_sm',
    'nl' : 'nl_core_news_lg',           # 'nl_core_news_sm',
    'en' : 'en_core_web_trf',           # 'en_core_web_sm',
    'fi' : 'fi_core_news_lg',           # 'fi_core_news_sm',
    'fr' : 'fr_dep_news_trf',           # 'fr_core_news_sm',
    'de' : 'de_dep_news_trf',           # 'de_core_news_sm',
    'el' : 'el_core_news_lg',           # 'el_core_news_sm',
    'it' : 'it_core_news_lg',           # 'it_core_news_sm',
    'ja' : 'ja_core_news_trf',          # 'ja_core_news_sm',
    'ko' : 'ko_core_news_lg',           # 'ko_core_news_sm',
    'lt' : 'lt_core_news_lg',           # 'lt_core_news_sm',
    'mk' : 'mk_core_news_lg',           # 'mk_core_news_sm',
    'no' : 'nb_core_news_lg',           # 'nb_core_news_sm',
    'nb' : 'nb_core_news_lg',           # 'nb_core_news_sm',
    'nn' : 'nb_core_news_lg',           # 'nb_core_news_sm',
    # TODO: provide language model for nn
    # https://github.com/ltgoslo/norne
    'pl' : 'nb_core_news_lg',           # 'pl_core_news_sm',
    'pt' : 'pt_core_news_lg',           # 'pt_core_news_sm',
    'ro' : 'ro_core_news_lg',           # 'ro_core_news_sm',
    'ru' : 'ru_core_news_lg',           # 'ru_core_news_sm',
    'es' : 'es_dep_news_trf',           # 'es_core_news_sm',
    'sv' : 'sv_core_news_lg',           # 'sv_core_news_sm',
    #'uk' : 'uk_core_news_sm',
    'multi-language' : 'xx_sent_ud_sm'} # 'xx_ent_wiki_sm'}

# RX



_ACRONYM_RX = re.compile(r'^[A-ZÆØÅ]{2,}([-/][A-ZÆØÅ]{2,})*$')
_ALNUM_RX = re.compile(r'\w', re.UNICODE)
_ALPHA_TYPE_RX = re.compile(r'^[aA]$')
_ALPHA_RX  = re.compile(r"^\s*[a-z]\s*[\)\.]?\s*", re.I)       # a)  b.  etc.
ANSWER_HEAD_RX = re.compile(r'\b(fasit|svar|løysings?-?forslag|solutions?|answer(?:\s*key)?)\b', re.I)
_ANSWER_RX = re.compile(r'\banswer(s)?\b', re.I)  # epub:type ~ "answer" / "answers"
_BLANK_SENTENCE_RX = re.compile(r"(?:_{2,}|\.{4,}|…)", re.UNICODE)  # matcher __, ...., … (fra §2.5.1.7)
BOOK_RX  = re.compile(r'\b(scan|scanned|page[-_ ]?scan|book[-_ ]?page|bokside|facsimile|faksimile)\b', re.I)
_BOX_CHARS = "□☐⬜◻▢▯⎕"
BOX_RX     = re.compile(rf"[{_BOX_CHARS}]+")
_BULLET_CHARS = "•●○–—\\-▪■‣∙·*‒•"  # utvidbar
_BULLET_PREFIX_RX = re.compile(rf'^\s*([{_BULLET_CHARS}]+)\s+')
COMIC_RX = re.compile(r'\b(comic|panel|strip|frame|speech\s*bubble|speechballoon|balloon|rute)\b',re.I)
#COMIC_RX = re.compile(r'\b(comic|panel|strip|graphic|manga|manhua|manhwa|teikneserie|tegn(?:e)?serie)\b', re.I)
_CONJ_PREFIX_RX = re.compile(r'^\s*(?:og|samt)\s*([A-Za-z])\)\s*')  # "og c)" / "samt d)"
DRAW_RX  = re.compile(r'\b(drawing|sketch|tegning|teikning)\b', re.I)
ELLIPSIS_RX = re.compile(r"(…+|\.\s?\.\s?\.\s?(?:\.\s?)*)")  # '…' eller '...' med/uten mellomrom, 3+ dots → '....'
EOS_PUNCT_RX = re.compile(r'([.!?…]+)([)"»’\]\)]*)\s*$')  # punktum/utrop/spm/ellipser + evt. lukkere
_FIGTEXT_CLASS_RX = re.compile(r'\b(caption|legend|figure[-_ ]?text|fig[-_ ]?desc|image[-_ ]?(desc|text))\b',re.I)
#_FIGTEXT_CLASS_RX = re.compile(r'\bfig(?:ure)?[-_ ]?(?:desc|text)\b', re.I)
_FIGTEXT_RX = re.compile(r'\bfig(?:ure)?[-_ ]?(?:desc|text)\b', re.I)
FIG_RX   = re.compile(r'\b(figure|diagram|graph|chart|plot|model|modell|schema|schematic|flow|kurve)\b', re.I)
GRAPH_RX = re.compile(r'\b(graph|chart|plot|diagram|kurve|søyle|linje(?:diagram)?|sektor(?:diagram)?)\b', re.I)
_H_RX = re.compile(r"^h([1-6])$", re.I)
HEADING_RX           = re.compile(r"^h([1-6])$", re.I)
_HEADING_RX = re.compile(r'^h([1-6])$', re.I)
ICON_RX  = re.compile(r'\b(icon|symbol|glyph|bullet|favicon|btn|button|arrow|chevron|caret|social|nav|menu)\b', re.I)
ILL_RX   = re.compile(r'\b(illustration|illustrasjon|illustrasjoner|illustrasjonar)\b', re.I)
_IMAGE_CREDITS_HEAD_RX = re.compile(r'^(?:image|picture|photo|illustration)s?\s+credits$|^(?:bilde|bilete|illustrasjons?)kreditt(?:er|ering|ar)?$',re.I)
_INDEX_HEAD_RX = re.compile(r'^(?:index|register|stikkordregister|sakregister|personregister|namneregister|navneregister)s?$', re.I)
_IPA_CORE_CLASS = r"A-Za-z\u0250-\u02AF\u02B0-\u02FF\u1D00-\u1DBF\u0300-\u036Fːˑˈˌ\u02C8\u02CC"  # inkluder stress/length
_IPA_SLASH_RX   = re.compile(rf"/([\s{_IPA_CORE_CLASS}]+?)/", re.DOTALL)
_IPA_BRACK_RX   = re.compile(rf"\[([\s{_IPA_CORE_CLASS}]+?)\]", re.DOTALL)
_LATIN_RX = re.compile(r"[A-Za-z\u00C0-\u024F]")
_LEADERS_RX = re.compile(r'[\.\u2022\u00B7·•…]+')  # ., bullets, middot, ellipsis, etc.
_LEADING_NUM_RX = re.compile(r"^\s*\d+[\.\):]?\s*")
LIST_LEADER_RX = re.compile(r'^\s*((\d+|[ivxlcdm]+|[a-z])[\.\)])\s+', re.I) # TODO: merge
LOGO_RX  = re.compile(r'\b(logo|logotype|brandmark)\b', re.I)
_LST_NONE_RX   = re.compile(r'list-style-type\s*:\s*none', re.I)
MAP_RX = re.compile(r'\b(map|kart|oversiktskart|atlas|globe|verdenskart|rutekart|områdekart|plan|plankart)\b',re.I)
_MIX_ALNUM_RX = re.compile(r"(?i)^(?=.*[A-Za-zÆØÅæøå])(?=.*\d)[A-Za-zÆØÅæøå0-9]+$")
_NONSTD_ALNUM_RX = re.compile(r'^(?=.*\d)(?=.*[A-Za-z])[A-Za-z0-9]+[\.]?$')  # 1A, A1, 1B., B12
_NONSTD_HIER_RX  = re.compile(r'^\d+(?:\.\d+){1,}$')                          # 2.1, 1.2.3
_NUM_PREFIX_RX = re.compile(r"^\s*(\d+)[\.\):]?\s*(.*)$")
_PARENS_BLOCK_RX   = re.compile(r"\((.*?)\)\s*$")                   # parentes på slutten av tekst
_PLAIN_CLASSES = {"plain", "list-unstyled", "list-style-type-none", "list-style-none"}
_PUNCT_RX = re.compile(r'([.!?])$')
#_PUNCT_RX = r'[.\)\:\-\u00A0]'  # godta . ) : - NBSP som skilletegn
QUOTE_BORDER_RX = re.compile(r'^[«“"”].*[»”"]$', re.S)
REF_HEAD_RX    = re.compile(r'\b(references?|bibliography|kilder|litteratur(?:liste)?|referans[ea]r|ordliste|glossary|stikkordregister|register|index)\b', re.I)
_RN_SUSPECT_RX = re.compile(r"(?i)[A-Za-zÆØÅæøå]rn[A-Za-zÆØÅæøå]")
_ROMAN_RX = re.compile(r'^(?=[ivxlcdm]+[\.\)])[ivxlcdm]+[\.\)]$', re.I)
#_ROMAN_RX = re.compile(r'^(?=[IVXLCDM]+$)M{0,4}(CM|CD|D?C{0,3})(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})$')
#_ROMAN_RX  = re.compile(r"^\s*[ivxlcdm]+\s*[\)\.]?\s*", re.I)  # iv)  ix.  etc.
_ROMAN_VALID_RX = re.compile(r'^(?=[IVXLCDM]+$)M{0,4}(CM|CD|D?C{0,3})(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})$')
_ROMAN_SIMPLE_RX = re.compile(r'(?i)^(?:M{0,4}(?:CM|CD|D?C{0,3})(?:XC|XL|L?X{0,3})(?:IX|IV|V?I{0,3}))$')
_SPEAKER_RX = re.compile(r"^\s*([A-ZÆØÅ][\wÆØÅæøå\.\- ]{1,50}?)\s*([:–—-])\s+",flags=re.UNICODE)
SPREADSHEET_RX = re.compile(r'\b(spreadsheet|sheet|excel|xls|regneark|tabell)\b', re.I)
_STD_ALPHA_RX   = re.compile(r'^[A-Za-z][.)]$')      # a)  A.
_STD_DECIMAL_RX = re.compile(r'^\d+[.)]$')           # 1.  2)
_STD_INT_TOKEN_RX   = re.compile(r'^\s*\d+[\.\):]?\s+')   # 1.  / 1)  / 1:
_STD_ROMAN_RX   = re.compile(r'^[ivxlcdm]+[.)]$', re.IGNORECASE)  # iv)  IX.
_STD_ROMAN_TOKEN_RX = re.compile(r'^\s*[IVXLCDM]+[\.\):]\s+', re.I)  # IX. / iv)
TASK_HEADINGS_RX = re.compile(r'\b(oppgaver|oppgåver|oppdrag|øvingar|øvinger|tasks?|exercises?|problems?)\b',re.I)
TASK_HEAD_RX   = re.compile(r'\b(oppgaver|oppgåver|øving(ar|er)?|tasks?|exercises?|problems?|questions?)\b', re.I) # TODO: merge
_TOK_RX     = re.compile(r'([A-Za-zÆØÅæøå]+)|(\s+)|([^\sA-Za-zÆØÅæøå]+)')
_TOKEN_RX = re.compile(r"[A-Za-zÆØÅæøå0-9]+", re.UNICODE) # TODO: merge
TRAILING_LINE_RX = re.compile(rf"(\s*(?:[_]{{3,}}|[–—-]{{3,}}|(?:\. ?){{5,}}|…{{2,}}|[{_BOX_CHARS}]{{2,}})\s*)+$")
PHOTO_RX = re.compile(r'\b(foto|photograph|photo|bilde|bilete|image|illustrasjon|illustration|portrett|portrait)\b',re.I)
_PUNCT_ONLY_RX = re.compile(r'^\s*[-–—·•.,;:!?…()\[\]{}"«»“”‘’]+\s*$')
SENT_SPLIT_RX = re.compile(r'([.!?…]+[)"»’\]\)]*)(\s+)')  # grense for splitting i ren tekst
_SKIP_INSIDE = {"code", "pre", "math", "kbd", "samp", "var"}
SUSPECT_STYLE_RX = re.compile(r'(position\s*:\s*absolute|float\s*:|top\s*:|left\s*:|column-count\s*:)', re.I)
_UC_LETTER_PREFIX_RX = re.compile(r"^\s*([A-ZÆØÅ])\b")
WEB_RX   = re.compile(r'\b(screenshot|screen[-_ ]?shot|web(?:page|side)?|nett[ -]?side|browser|url)\b', re.I)
_WIDE_RX = re.compile(rf'^\s*([0-9]+|[A-Za-z]|[ivxlcdmIVXLCDM]+)\s*(?:{_PUNCT_RX}+)?\s+')
#_WIDE_RX:  r'^\s*([0-9]+|[A-Za-z]|[ivxlcdmIVXLCDM]+)\s*(?:[.\)\:\-\u00A0]+)?\s+'
_WORD_SPLIT_RX     = re.compile(r"[;,/]|(?:\s{2,})")                # delere for “gitt ord”

_NONSTD_TOKEN_RX    = re.compile(
    r'^\s*(?:'            # start
    r'\d+[A-Za-z]'        # 1A, 10a, 2b
    r'|'                  
    r'(?:\d+\.)+\d+[A-Za-z]?'  # 2.10c, 3.2, 4.5.1
    r'|'                  
    r'[A-Za-z]\d+'        # A1, B12
    r')'
)

_EXAMPLE_PREFIX_RX = re.compile(
    r"^\s*(?:"
    r"svar(?:et)?|fasit|eksempel(?:svar)?|døme(?:\s*på\s*svar)?|"
    r"answer|example\s+answer|sample\s+answer|model\s+answer|example"
    r")\s*[:\-–—]?\s*",
    re.IGNORECASE
)

_SOURCE_PREFIX_RX = re.compile(
    r"""^\s*(
        (kilde|kjelde|source|foto|fotograf|illustrasjon|illu\.?|bilde|copyright|©)
        \s*[:\-–]?
    )\s*""",
    re.IGNORECASE | re.VERBOSE
)


_JUNK_ALT_RXES = [
    re.compile(r'^\s*$', re.I),                 # tomt
    re.compile(r'^(image|img|picture|bilde)$', re.I),
    re.compile(r'.+\.(jpg|jpeg|png|gif|svg|webp)$', re.I),  # filnavn
]
_NUMERIC_MIX_OCR_RXES = [
    re.compile(r"\d[OIlS]\d"),
    re.compile(r"[A-Za-zÆØÅæøå]0[A-Za-zÆØÅæøå]"),
]

# TAGS
_SKIP_TAGS = {"code", "pre", "math", "svg", "style", "script"}  # TODO: merge
_SKIP_ANCESTORS = {"code", "pre", "math", "script", "style", "kbd", "samp", "var", "textarea"}
_SKIP_CONTAINERS = {"math", "pre", "code", "figure"}
_VALID_BLOCK_PARENTS = {"body","section","article","div","li","aside","td","th","main","header","footer"}
_CONTENT_TAGS  = {"img","svg","math","table","code","kbd","samp","var","object","embed","canvas","audio","video","iframe","sup","sub","abbr"}
_PROTECTED = {"code", "pre", "math", "kbd", "samp", "var"}
#_PROTECTED = {"code", "pre", "math", "script", "style", "textarea", "kbd", "samp", "var"}
#_PROTECTED = {"pre", "code", "math", "script", "style", "textarea"}
# PROTECTED = {"code", "pre", "math", "script", "style", "textarea"}
_PROTECTED_ANCESTORS = {"code", "pre", "math", "script", "style", "textarea", "nav"}
#_BLOCKY = {"ul", "ol", "table", "div", "section", "aside", "dl", "figure"}
_BLOCKY = {
    "p", "div", "section", "article", "aside", "figure",
    "header", "footer", "nav", "table", "ul", "ol", "dl", "blockquote",
    "main", "pre", "form", "details", "summary"
}
_BLOCK_TAGS = {
    "address","article","aside","blockquote","canvas","div","dl","fieldset",
    "figcaption","figure","footer","form","h1","h2","h3","h4","h5","h6",
    "header","hr","li","main","nav","noscript","ol","p","pre","section",
    "table","tbody","thead","tfoot","tr","th","td","ul"
}
#_BLOCKY = {"ul", "ol", "table", "figure", "blockquote", "section",
#           "aside", "dl", "pre", "math"}

# DIV
_BLANK_MARKERS = {
    "blank side.",
    "innhaldet på denne sida har blitt flytta.",
    "innholdet på denne siden har blitt flyttet.",
}
CLOSERS = set(')"»’])')
NBSP = '\u00A0'
_BEFORE_ALTS = (
    r'§{1,2}', r'kr\.?', r'nok', r'eur', r'usd', r'gbp', r'€', r'\$', r'£',
    r's\.', r'kap\.', r'nr\.', r'pkt\.', r'fig\.', r'tab\.', r'kl\.', r'ca\.'
)
_AFTER_ALTS = (
    r'kg', r'g', r'mg',
    r'km', r'm', r'cm', r'mm',
    r'km²', r'm²', r'cm²', r'km³', r'm³',
    r'°c', r'°f', r'%', r'ppm',
    r's', r'ms', r'min', r'h', r't', r'år', r'mnd', r'uke',
    r'kr', r'nok', r'eur', r'usd', r'gbp', r'€', r'\$', r'£'
)
RE_BEFORE = re.compile(
    rf'(?<!\w)({"|".join(_BEFORE_ALTS)})\s+(?=\d)',  # ingen word-char før; minst ett space; foran et siffer
    flags=re.IGNORECASE
)
RE_AFTER = re.compile(
    rf'(?<=\d)\s+({"|".join(_AFTER_ALTS)})(?=$|[^\w])',
    flags=re.IGNORECASE
)

TASK_TYPES   = {"practice","exercise","exercises","task","tasks","assessment","questions","problems"}
ANSWER_TYPES = {"answer","answers","solution","solutions"}
REF_TYPES    = {"bibliography","references","reference","glossary","index"}

_SCRIPT_LANGS = [
    ("el", re.compile(r"[\u0370-\u03FF]")),   # Greek
    ("ru", re.compile(r"[\u0400-\u04FF]")),   # Cyrillic (ru som nøytral)
    ("he", re.compile(r"[\u0590-\u05FF]")),   # Hebrew
    ("ar", re.compile(r"[\u0600-\u06FF]")),   # Arabic
    ("hi", re.compile(r"[\u0900-\u097F]")),   # Devanagari (Hindi)
    ("th", re.compile(r"[\u0E00-\u0E7F]")),   # Thai
    ("ja", re.compile(r"[\u3040-\u30FF]")),   # Hiragana/Katakana
    ("zh", re.compile(r"[\u4E00-\u9FFF]")),   # CJK Unified Ideographs
]

_EN_STOP = {"the","and","to","of","in","on","for","with","is","are","was",
            "were","as","by","at","from","that","this"}

_ALLOWED_MIX = {
    "h2o","co2","so2","o2","o3","no2","pm2","pm2.5","2d","3d","4g","5g","g20"
}

_CROSSWORD_TOKENS = {"crossword", "puzzle-crossword", "crossword-puzzle"}
_STOPNAME_TOKENS = {
    # skolefaglige
    "oppgave","oppgåve","eksempel","figur","tabell","definisjon","teorem","setning",
    "bevis","hint","løysing","løsning","kapittel","del","side","kommentar","merknad",
    # typiske matte-/naturfag-etiketter (enbokstav)
    "v","a","m","n","x","y","z","f","g","h","u","s","t","r","p","q","k"
}
TASK_ITEM_TYPES      = {"assessment", "exercise", "question", "task", "problem"}
TASK_CONTAINER_TYPES = {"assessments", "exercises", "tasks"}  # grupper/bolker
_ALLOWED_ALTS = {"photo","illustration","figure","symbol","map","drawing","comic","logo"}
TASK_TOKENS = {
    "assessment","assessments",
    "exercise","exercises",
    "question","questions",
    "task","tasks",
    "problem","problems",
    "answer","answers","fasit"  # hvis dere bruker epub:type for fasit
}
_TASK_TOKENS = {
    "assessment", "assessments",
    "exercise", "exercises",
    "practice",
    "task", "tasks",
    "fill-in-the-blank-problem",
}
TASKISH_TOKENS = {
    "assessment","assessments",
    "exercise","exercises",
    "practice","task","tasks",
    "question","questions",
    "answer","answers","key","fasit"
}
_TASKISH_TOKENS = {"assessment","assessments","exercise","exercises","practice","task","tasks"}

_MARGIN_CLASS_TOKENS = {
    "margin", "marginalia", "marg", "sidekommentar", "merknad", "kommentar",
    "comment", "sidebar-note", "note-margin"
}
_MARGIN_TYPE_TOKENS = {"annotation", "marginalia", "sidebar", "note", "comment"}
_ANSWER_TOKENS = {"answer", "answers", "solution", "solutions", "fasit"}
_ANSWERISH_TOKENS = {"answer","answers","key","fasit"}
_EXAMPLEISH_TOKENS = {"example","sample","model"}
EMPTY_TOKENS = {"", "-", "–", "—", ".", "…", "•", "·", "\u00A0"}
_PLAY_HEADING_TOKENS = {
    "skuespill","drama","scene","akt","dialog","manus","replikk","roller","personer",
    "dramatis personae","cast","characters","play"
}
_FILL_TOKENS = {"fill-in-the-blank-problem"}
_BAD_BLOCKS = {
    "p", "ul", "ol", "dl",
    "table", "thead", "tbody", "tfoot", "tr", "td", "th",
    "blockquote", "pre",
    "section", "article", "details", "summary",
    "figure"  # nested figure
}
_BULLET_RX = re.compile(rf"^\s*([{_BULLET_CHARS}]+)\s+")
_GLOSSARY_TITLES = {
    "en": "Glossary",
    "nn": "Ordforklaringar",
    "nb": "Ordforklaringer",
    "no": "Ordforklaringer",
}
_GENERIC_ALT = {"symbol", "ikon", "oppgavesymbol", "task symbol", "icon"}  # kan utvides
_MATCH_TOKENS = {"match-problem"}  # kan utvides: {"match-problem","matching","pairing"}
BOARD_CLASS_HINTS = {"boardgame", "board-game", "gameboard", "game-board"}
BOX_CLASS_HINTS   = {"box", "tile", "square", "space", "cell"}
_CHECK_GLYPHS = set("☐☑☒✓✔✗✘")
_FRAME_ALLOWED = {"generisk-ramme", "ramme", "bg-red", "bg-blue", "bg-yellow", "bg-gray", "bg-beige"}
_GRAM_LABELS = {
    "FS","F","V","S","P","O","DO","IO","ADV","A","OBJ","SUBJ","K","C","PP","PR"
}
_PRON_SETS = {
    "no": {"jeg","du","han","hun","vi","dere","de"},
    "nn": {"eg","du","han","ho","vi","de","dei","dåkker"},  # nn-varianter
    "sv": {"jag","du","han","hon","vi","ni","de"},
    "da": {"jeg","du","han","hun","vi","i","de"},
    "en": {"i","you","he","she","it","we","they"},
    "de": {"ich","du","er","sie","es","wir","ihr","sie"},
    "fr": {"je","tu","il","elle","on","nous","vous","ils","elles"},
    "es": {"yo","tú","tu","él","ella","usted","nosotros","nosotras","vosotros","vosotras","ellos","ellas","ustedes"},
    "it": {"io","tu","lui","lei","noi","voi","loro"},
}
_ALL_PRONS = set().union(*_PRON_SETS.values())

# ----------------


# FUNCTIONS
# =========

is_task         = lambda tag: 'epub:type' in tag.attrs.keys() and tag['epub:type'] in ASSESSMENTS
is_part_of_task = lambda tag: any([('epub:type' in parent.attrs.keys() and parent['epub:type'] in ASSESSMENTS) for parent in tag.parents])
has_subtasks    = lambda tag: tag.find(attrs={'epub:type':ASSESSMENTS})
get_tasks       = lambda soup: list(soup(attrs={'class': re.compile(r'^assignment')})) + list(soup(attrs={'epub:type':ASSESSMENTS}))
get_answers     = lambda soup: list(soup(attrs={'epub:type':'answer'})) + list(soup(attrs={'epub:type':'answers'}))

# --- Logging ------------------------------------------------------

def configure_logging(verbosity: int) -> None:
    """
    verbosity: 0 -> WARNING, 1 -> INFO, 2+ -> DEBUG
    """
    if verbosity <= 0:
        level = WARNING
    elif verbosity == 1:
        level = INFO
    else:
        level = DEBUG

    root = getLogger()
    root.setLevel(level)

    # Opprett én StreamHandler hvis ingen finnes, ellers oppdater nivå/formatter på eksisterende
    fmt = Formatter('%(asctime)s %(levelname)s [%(name)s] %(message)s',
                            datefmt='%H:%M:%S')

    if not root.handlers:
        h = StreamHandler()
        h.setLevel(level)
        h.setFormatter(fmt)
        root.addHandler(h)
    else:
        for h in root.handlers:
            try:
                h.setLevel(level)
                h.setFormatter(fmt)
            except Exception:
                pass

    # Dempe støy fra tredjepart (skrues bare opp hvis du faktisk ber om DEBUG)
    noisy = ('urllib3', 'pika', 'bs4')
    for n in noisy:
        getLogger(n).setLevel(WARNING if level < DEBUG else INFO)

# --- Valgfri LLM-hjelper ------------------------------------------------------

class _NoopLLM:
    available = False
    def classify_aside_integral(self, html_snippet, prev_snip, next_snip):
        # Ingen LLM: alltid "ikke integral" -> flytt
        return {"integral": False, "confidence": 0.0}

def _ensure_llm_client(logger, use_llm):
    if not use_llm:
        return _NoopLLM()
    try:
        class LLMRpcClient:
            available = True
            def __init__(self, host="localhost", port=5672, user="admin", password="admin", queue="llm_tasks"):
                creds = PlainCredentials(user, password)
                self.conn = BlockingConnection(ConnectionParameters(host=host, port=port, credentials=creds))
                self.channel = self.conn.channel()
                self.queue = queue
                result = self.channel.queue_declare(queue="", exclusive=True)
                self.callback_queue = result.method.queue
                self.responses = {}
                self.channel.basic_consume(
                    queue=self.callback_queue,
                    on_message_callback=self._on_response,
                    auto_ack=True
                )

            def _on_response(self, ch, method, props, body):
                self.responses[props.correlation_id] = body

            def _rpc(self, payload: dict, timeout=8.0):
                corr_id = str(uuid.uuid4())
                self.channel.basic_publish(
                    exchange="",
                    routing_key=self.queue,
                    properties=pika.BasicProperties(
                        reply_to=self.callback_queue,
                        correlation_id=corr_id,
                        content_type="application/json"
                    ),
                    body=json.dumps(payload).encode("utf-8")
                )
                # Vent synkront i kort tid (lav latenstid lokalt)
                start = time()
                while corr_id not in self.responses:
                    self.conn.process_data_events(time_limit=0.2)
                    if (time() - start) > timeout:
                        raise TimeoutError("LLM RPC timeout")
                body = self.responses.pop(corr_id)
                return json.loads(body.decode("utf-8"))

            def classify_aside_integral(self, html_snippet, prev_snip, next_snip):
                """
                Returnerer f.eks. {"integral": true/false, "confidence": 0.0-1.0}
                """
                payload = {
                    "action": "classify_aside_integral",
                    "html": html_snippet,
                    "prev": prev_snip,
                    "next": next_snip
                }
                try:
                    return self._rpc(payload)
                except Exception as e:
                    logger.warning(f"2.1.2 - LLM unavailable ({e}); continuing without it.")
                    return {"integral": False, "confidence": 0.0}

        return LLMRpcClient()
    except Exception as e:
        logger.warning(f"Could not initialize LLM client: {e}. Running without LLM.")
        return _NoopLLM()

def find_xhtml(production_number, epub_folder, logger):
    logger.debug(f'Finding xhtml file for {production_number}')
    for root, _, files in walk(epub_folder):
        for file in [f for f in files if f.endswith('.xhtml')]:
            if file == f'{production_number}.xhtml':
                return path.join(root, file)
    logger.error('No xhtml file found in the temporary directory.')
    print('No xhtml file found in the temporary directory.')
    quit()

def find_folder(start_dir, target_folder):
    for root, dirs, files in walk(start_dir):
        if target_folder in dirs:
            return path.join(root, target_folder)
    return None

# TODO: This does not really work. FIX
def find_header_level(tag, logger):
    logger.debug(f'Finding header level for {tag}')
    for element in [tag] + list(tag.parents):
        for sibling in list(element.find_previous_siblings()) + list(element.find_next_siblings()):
            if (h := sibling.find(re.compile(r'^h[1-6]$'))):
                return h.name[1] if element == tag else str(int(h.name[1]) + 1) if h.name[1] != '6' else '6'
    logger.error(f'No header level found for {tag}')
    return '2' # TODO: find proper heading level

def original_page(tag, soup, logger):
    page        = '?'
    decrement   = -1
    pagebreak   = None
    if (pagebreak   := tag.find_previous(attrs = {'epub:type':'pagebreak'})):
        decrement = 0
    elif (pagebreak := tag.find_next(attrs = {'epub:type':'pagebreak'})):
        decrement = 1

    if pagebreak:
        if 'title' in pagebreak.attrs.keys():
            page =  str(int(pagebreak['title']) - decrement)
        elif 'id' in pagebreak.attrs.keys():
            # TODO: check pagebreak['id'] for other languages
            # page =  str(int(pagebreak['id'].split('-')[-1]).group() - decrement)
            return '?'
        else:
            pbs = 0
            for soup in nordic.content:
                for pb in soup(attrs = {'epub:type':'pagebreak'}):
                    pbs += 1
                    if pb == pagebreak:
                        page = str(pbs)
    return page

def get_heading(tag, soup, logger):
    # The specification only gives two option, but here we have the
    # possibility to expand the range of languages, thus:
    #   page = pages[soup.html['lang']] if soup.html['lang'] in pages.keys() else pages['en']

    page = PAGES['en'] if soup.html['lang'] == 'en' else PAGES['no']
    return page + ' ' + original_page(tag, soup, logger) + ':'


def figure_to_table(docs, soup, figure):
    try:
        # =====================================================================
        # This part of the method is implemented using this article as a basis:
        # https://towardsdatascience.com/a-table-detection-cell-recognition-and-text-extraction-algorithm-to-convert-tables-to-excel-files-902edcf289ec
        # - viewed 04.05.2023

        # Reading file
        img = cv2.imread(docs + figure.img['src'], 0)
        img.shape

        # Thresholding the image to a binary image
        thresh,img_bin = cv2.threshold(img,128,255,cv2.THRESH_BINARY | cv2.THRESH_OTSU)

        # Inverting the image
        img_bin = 255-img_bin

        # countcol(width) of kernel as 100th of total width
        kernel_len  = np.array(img).shape[1]//100
        # Defining a vertical kernel to detect all vertical lines of image
        ver_kernel  = cv2.getStructuringElement(cv2.MORPH_RECT, (1, kernel_len))
        # Defining a horizontal kernel to detect all horizontal lines of image
        hor_kernel  = cv2.getStructuringElement(cv2.MORPH_RECT, (kernel_len, 1))
        # A kernel of 2x2
        kernel      = cv2.getStructuringElement(cv2.MORPH_RECT, (2, 2))

        #Use vertical kernel to detect and save the vertical lines in a jpg
        image_1         = cv2.erode(img_bin, ver_kernel, iterations=3)
        vertical_lines  = cv2.dilate(image_1, ver_kernel, iterations=3)

        #Use horizontal kernel to detect and save the horizontal lines in a jpg
        image_2             = cv2.erode(img_bin, hor_kernel, iterations=3)
        horizontal_lines    = cv2.dilate(image_2, hor_kernel, iterations=3)

        # Combine horizontal and vertical lines in a new third image, with both having same weight.
        img_vh          = cv2.addWeighted(vertical_lines, 0.5, horizontal_lines, 0.5, 0.0)
        img_vh          = cv2.erode(~img_vh, kernel, iterations=2)
        thresh, img_vh  = cv2.threshold(img_vh,128,255, cv2.THRESH_BINARY | cv2.THRESH_OTSU)
        bitxor          = cv2.bitwise_xor(img,img_vh)
        bitnot          = cv2.bitwise_not(bitxor)

        # Detect contours for following box detection
        contours, hierarchy = cv2.findContours(img_vh, cv2.RETR_TREE, cv2.CHAIN_APPROX_SIMPLE)

        def sort_contours(cnts, method='left-to-right'):
            # handle if we need to sort in reverse
            reverse = True  if method in ['right-to-left', 'bottom-to-top'] else False
            # handle if we are sorting against the y-coordinate rather than
            # the x-coordinate of the bounding box
            i       = 1     if method in ['top-to-bottom', 'bottom-to-top'] else 0

            # construct the list of bounding boxes and sort them from top to
            # bottom
            boundingBoxes           = [cv2.boundingRect(c) for c in cnts]
            (cnts, boundingBoxes)   = zip(*sorted(
                zip(cnts, boundingBoxes),
                key=lambda b:b[1][i], reverse=reverse))


            # return the list of sorted contours and bounding boxes
            return (cnts, boundingBoxes)

        # Sort all the contours by top to bottom.
        contours, boundingBoxes = sort_contours(contours, method='top-to-bottom')

        #Creating a list of heights for all detected boxes
        heights = [boundingBoxes[i][3] for i in range(len(boundingBoxes))]

        #Get mean of heights
        mean = np.mean(heights)

        #Create list box to store all boxes in
        box = []
        # Get position (x,y), width and height for every contour and show the contour on image
        for c in contours:
            x, y, w, h = cv2.boundingRect(c)
            if (w<1000 and h<500):
                image = cv2.rectangle(img,(x,y),(x+w,y+h),(0,255,0),2)
                box.append([x,y,w,h])

        #Creating two lists to define row and column in which cell is located
        row     = []
        column  = []
        j       = 0

        #Sorting the boxes to their respective row and column
        for i in range(len(box)):
            if i == 0:
                column.append(box[i])
                previous = box[i]
            else:
                if(box[i][1] <= previous[1] + mean/2):
                    column.append(box[i])
                    previous = box[i]
                    if i == len(box)-1:
                        row.append(column)
                else:
                    row.append(column)
                    column      = []
                    previous    = box[i]
                    column.append(box[i])

        #calculating maximum number of cells
        countcol = 0
        for i in range(len(row)):
            countcol = len(row[i])
            if countcol > countcol:
                countcol = countcol

        #Retrieving the center of each column
        center = [int(row[i][j][0]+row[i][j][2]/2) for j in range(len(row[i])) if row[0]]
        center = np.array(center)
        center.sort()

        #Regarding the distance to the columns center, the boxes are arranged in respective order
        finalboxes = []
        for i in range(len(row)):
            lis = []
            for k in range(countcol):
                lis.append([])
            for j in range(len(row[i])):
                diff        = abs(center-(row[i][j][0]+row[i][j][2]/4))
                minimum     = min(diff)
                indexing    = list(diff).index(minimum)
                lis[indexing].append(row[i][j])
            finalboxes.append(lis)

        #from every single image-based cell/box the strings are extracted via pytesseract and stored in a list
        outer = []
        for i in range(len(finalboxes)):
            for j in range(len(finalboxes[i])):
                inner = ''
                if(len(finalboxes[i][j])==0):
                    outer.append(' ')
                else:
                    for k in range(len(finalboxes[i][j])):
                        y = finalboxes[i][j][k][0]
                        x = finalboxes[i][j][k][1]
                        w = finalboxes[i][j][k][2]
                        h = finalboxes[i][j][k][3]

                        finalimg    = bitnot[x:x+h, y:y+w]
                        kernel      = cv2.getStructuringElement(cv2.MORPH_RECT, (2, 1))
                        border      = cv2.copyMakeBorder(finalimg,2,2,2,2, cv2.BORDER_CONSTANT,value=[255,255])
                        resizing    = cv2.resize(border, None, fx=2, fy=2, interpolation=cv2.INTER_CUBIC)
                        dilation    = cv2.dilate(resizing, kernel,iterations=1)
                        erosion     = cv2.erode(dilation, kernel,iterations=2)

                        out = pytesseract.image_to_string(erosion)
                        if(len(out)==0):
                            out = pytesseract.image_to_string(erosion, config='--psm 3')
                        inner = inner + ' ' + out
                    outer.append(inner)

        #Creating a dataframe of the generated OCR list
        arr     = np.array(outer)
        df      = pd.DataFrame(arr.reshape(len(row), countcol))
        data    = df.style.set_properties(align='left')

        # End of quoted method
        # =====================================================================

        table = BeautifulSoup(df.to_html(), 'html.parser')

        # TODO: Find better test
        return table if len(table('td', text=True)) * 4 > len(table('td', text=False)) else None

    except Exception as e: # work on python 3.x
        return None


# =============================================================================
# GENERIC HELPERS
# =============================================================================



def _get_text_snippet(tag, max_chars=240):
    # 2.1.2
    txt = (tag.get_text(" ", strip=True) or "").strip()
    return (txt[:max_chars] + "…") if len(txt) > max_chars else txt

def _is_task_heading(tag) -> bool:
    # 2.1.2
    # Overskrifter som utløser "plassér før oppgaver"
    if tag.name and tag.name.lower() in ('h1','h2','h3','h4','h5','h6'):
        if TASK_HEADINGS_RX.search(tag.get_text(" ", strip=True) or ""):
            return True
    # Vanlige semantiske markører
    cls = " ".join(tag.get("class", [])).lower()
    if any(k in cls for k in ("tasks", "task", "oppgaver", "oppgåver", "øving", "exercise", "exercises")):
        return True
    t = (tag.get("epub:type") or "").lower()
    if any(k in t for k in ("practice", "exercise", "tasks")):
        return True
    return False



def _tag_moved_origin(node):
    # 2.1.2
    """Merk noden med hvilket 'segment' (høyre sidebryter) den opprinnelig lå foran."""

    nxt = node.find_next(lambda x: getattr(x, "name", None) and _is_pagebreak(x))
    if nxt:
        seg_id = nxt.get("id")
        if seg_id:
            node.attrs["data-moved-from-seg"] = seg_id

def _is_glossary_container(tag):
    # 2.1.2
    # Enten en <dl>, eller et element som inneholder en <dl>
    if tag.name and tag.name.lower() == "dl":
        return True
    return tag.find("dl") is not None

def _is_acronym(tok: str) -> bool:
    # 2.1.3
    return bool(_ACRONYM_RX.match(tok)) or bool(_ROMAN_RX.match(tok))

def _is_pagebreak(tag: Tag) -> bool:
    if not isinstance(tag, Tag):
        return False
    t = (tag.get("epub:type") or "").lower()
    r = (tag.get("role") or "").lower()
    return ("pagebreak" in t) or (r == "doc-pagebreak")

def _iter_pagebreaks_in_order(soup):
    # 2.1.4
    # Stabil dokumentrekkefølge
    return [el for el in soup.find_all(True) if _is_pagebreak(el)]

def _collect_between(prev, curr):
    # 2.1.4
    """Samle noder mellom prev og curr i dokumentrekkefølge (ekskl. curr)."""
    nodes = []
    for x in prev.next_elements:
        if x is curr:
            break
        nodes.append(x)
    return nodes

def _has_visible_content(nodes):
    # 2.1.4
    """
    Returner (has_visible, ambiguous_text).
    'visible' = ikke-whitespace tekst eller reelt innhold (img, svg, math, table, lister, osv.)
    'ambiguous_text' = svært korte tekstfragmenter/punktum/pynt (kan brukes for evt. LLM).
    """
    text_bits = []
    for n in nodes:
        if isinstance(n, NavigableString):
            txt = str(n)
            if txt.strip():
                text_bits.append(txt.strip())
        elif getattr(n, "name", None):
            nm = n.name.lower()
            if _is_pagebreak(n):
                continue
            if nm in {"br","hr","nav"}:
                continue
            if nm in {"img","svg","math","table","ul","ol","li","pre","code","blockquote",
                      "audio","video","object","embed","canvas","iframe","figure"}:
                return True, ""
            # Tekstlig innhold inne i element
            if (n.get_text(strip=True) or ""):
                # Ikke alt tekstlig er "synlig nok" – vi samler og vurderer samlet under
                text_bits.append(n.get_text(" ", strip=True))
    # Samlet tekstlig vurdering
    combined = " ".join(text_bits).strip()
    if not combined:
        return False, ""
    # Hvis det bare er veldig kort/pynt: klass iffy
    # Eksempel: én bindestrek eller * * * – disse regner vi ikke som reelt innhold
    if len(combined) <= 5 and re.fullmatch(r"[-–—*•·\.]+", combined):
        return False, combined
    # Ellers: synlig tekst
    return True, ""

def _find_prev_significant(node):
    # 2.1.4
    """Finn forrige signifikante node (ignorer ren whitespace)."""
    cur = node.previous_sibling
    # BeautifulSoup kan ha mye whitespace som siblings
    while cur is not None:
        if isinstance(cur, NavigableString):
            if cur.strip():
                return cur
        elif getattr(cur, "name", None):
            # Returner første element-søsken
            return cur
        cur = cur.previous_sibling
    # Fall back: gå litt bredere om nødvendig
    return node.find_previous(lambda x: isinstance(x, NavigableString) and x.strip() or getattr(x, "name", None))

def _find_block_insertion_anchor(pagebreak):
    # 2.1.4
    """
    Sett inn <p> før nærmeste blokknivå-forelder som kan ta <p> som søsken.
    Dette unngår <p> inni <p>.
    """
    top = pagebreak
    while top.parent is not None and top.parent.name not in _VALID_BLOCK_PARENTS:
        top = top.parent
    return top  # vi setter inn 'before' denne

def _unwrap_nested_same_tags(soup, tagname):
    # 2.1.6
    # <em><em>... -> <em>...</em> ; <strong><strong>... -> <strong>...</strong>
    changed = 0
    for inner in list(soup.find_all(tagname)):
        parent = inner.parent
        if getattr(parent, "name", None) == tagname:
            inner.unwrap()
            changed += 1
    return changed

def _rightmost_text_node(tag):
    # 2.1.6.3
    # siste tekstnode inne i tag (dypt)
    for node in reversed(list(tag.descendants)):
        if isinstance(node, NavigableString):
            return node
    return None

def _leftmost_text_node(tag):
    # 2.1.6.3
    for node in tag.descendants:
        if isinstance(node, NavigableString):
            return node
    return None

def _is_toc_container(el) -> bool:
    # 2.1.7
    if not getattr(el, "name", None):
        return False
    t = (el.get("epub:type") or "").lower()
    if "toc" in t:
        return True
    role = (el.get("role") or "").lower()
    if role == "doc-toc":
        return True
    el_id = (el.get("id") or "").lower()
    if el_id in {"toc", "table-of-contents", "contents"}:
        return True
    cls = " ".join(el.get("class", [])).lower()
    if "toc" in cls:
        return True
    return False

def _normalize_caps_sentence_style(text: str) -> str:
    """
    Senk kun ord som er HELT VERSALER (>=2 bokstaver) og ikke akronymer/romertall.
    Behold første alfabetiske ord med stor forbokstav (setningsstil).
    """
    tokens = re.split(r'(\s+)', text)
    out, first_alpha = [], False
    for tok in tokens:
        if tok.strip() and tok.isalpha():
            if not first_alpha:
                if len(tok) > 1:
                    if tok.isupper() and not _is_acronym(tok):
                        tok = tok.lower()
                    tok = tok[0].upper() + tok[1:]
                else:
                    #pass # TESTING
                    tok = tok.upper()
                first_alpha = True
            else:
                if tok.isupper() and len(tok) > 1 and not _is_acronym(tok):
                    tok = tok.lower()
        out.append(tok)
    return "".join(out)

def _ensure_list_container(soup, toc_box):
    """
    Sørg for at TOC er en <ol class="list-style-type-none" style="list-style-type: none;">
    Konverter tabeller om nødvendig.
    Returnerer (ol_element, changed_bool).
    """
    # Finn eksisterende liste
    ol = toc_box.find(["ol", "ul"], recursive=False)
    if ol:
        # normaliser til <ol> med riktig styling
        if ol.name != "ol":
            new_ol = soup.new_tag("ol")
            new_ol.extend(list(ol.contents))
            ol.replace_with(new_ol)
            ol = new_ol
        # sett klassen/inline-styling (idempotent)
        cls = set(ol.get("class", []))
        cls.add("list-style-type-none")
        ol["class"] = list(cls)
        style = (ol.get("style") or "").strip()
        if "list-style-type: none;" not in style.replace(" ", ""):
            ol["style"] = (style + ("; " if style else "") + "list-style-type: none;").strip()
        return ol, False

    # Hvis tabell: konverter <table> -> <ol>
    table = toc_box.find("table")
    if table:
        ol = soup.new_tag("ol", **{"class": "list-style-type-none"})
        ol["style"] = "list-style-type: none;"
        # antatt: hver <tr> er en post
        for tr in table.find_all("tr"):
            cells = tr.find_all(["td", "th"])
            if not cells:
                continue
            # heuristikk: siste celle har sidehenvisning, resten er "tittel"
            title_text = " ".join(cells[i].get_text(" ", strip=True) for i in range(len(cells)-1))
            page_text = cells[-1].get_text(" ", strip=True)
            page_text = _LEADERS_RX.sub("", page_text).strip()
            li = soup.new_tag("li")
            a = soup.new_tag("a")
            # prøv å hente href hvis det finnes en lenke inne i raden
            link = tr.find("a", href=True)
            if link:
                a["href"] = link["href"]

            # bygg to spans
            s1 = soup.new_tag("span", **{"class": "lic"})
            s1.string = _normalize_caps_sentence_style(title_text).rstrip() + " "
            s2 = soup.new_tag("span", **{"class": "lic"})
            s2.string = page_text
            a.append(s1); a.append(s2)
            li.append(a)
            ol.append(li)
        table.replace_with(ol)
        return ol, True

    # Hvis ingen liste eller tabell, lag tom liste og flytt inn <li> hvis de finnes dypt
    ol = soup.new_tag("ol", **{"class": "list-style-type-none"})
    ol["style"] = "list-style-type: none;"
    # flytt over eksisterende <li> hvis de ligger dypt
    lis = toc_box.find_all("li")
    if lis:
        for li in lis:
            ol.append(li.extract())
    toc_box.append(ol)
    return ol, True

def _normalize_toc_li(soup, li):
    """
    Sørg for: <li><a href="#..."><span class="lic">Tittel </span> <span class="lic">9</span></a></li>
    """
    # Finn/lag <a>
    a = li.find("a", recursive=False)
    if not a:
        # prøv å hente en dypere a
        deep_a = li.find("a")
        if deep_a and deep_a.get("href"):
            a = deep_a
            # løft opp til direkte barn
            a.extract()
            for c in list(li.contents):
                c.extract()
            li.append(a)
        else:
            # ingen lenke: lag en "dummy"-a uten href
            a = soup.new_tag("a")
            # flytt alt inn
            for c in list(li.contents):
                a.append(c.extract())
            li.append(a)

    # Fjern bilder inne i li/a
    for img in a.find_all("img"):
        img.decompose()

    # Ekstraher ren tekst i a (uten spans), fjern ledere på slutten
    raw_text = a.get_text(" ", strip=True)
    raw_text = re.sub(r'\s+', ' ', raw_text).strip()

    # Hvis det allerede finnes to <span class="lic">: normaliser innholdet
    spans = a.find_all("span", class_="lic", recursive=False)
    if len(spans) >= 2:
        # første = tittel (trim og ett space til slutt), andre = side
        title = spans[0].get_text(" ", strip=True)
        page  = spans[1].get_text(" ", strip=True)
        page  = _LEADERS_RX.sub("", page).strip()
        spans[0].string = _normalize_caps_sentence_style(title).rstrip() + " "
        spans[1].string = page
        # fjern evt. overskytende spans
        for extra in spans[2:]:
            extra.decompose()
        return True

    # Ellers: forsøk å splitte ut sidehenvisning fra slutt av teksten
    tokens = raw_text.split()
    page = ""
    if tokens:
        last = tokens[-1]
        # stripp ledere fra siste token først
        last_clean = _LEADERS_RX.sub("", last).strip()

        if (t := last_clean.strip()) and (t.isdigit() or bool(_ROMAN_SIMPLE_RX.match(t))):
            page = last_clean
            title = " ".join(tokens[:-1]).strip()
        else:
            title = raw_text
    else:
        title = raw_text

    # Tøm a og bygg to spans
    for c in list(a.contents):
        c.extract()

    s1 = soup.new_tag("span", **{"class": "lic"})
    s1.string = _normalize_caps_sentence_style(title).rstrip() + " "
    a.append(s1)

    s2 = soup.new_tag("span", **{"class": "lic"})
    s2.string = page
    a.append(s2)

    return True

def _ensure_single_space_between_spans(a_tag):
    """
    Sørger for nøyaktig én plain space mellom *tilstøtende*
    <span class="lic"> … </span> i en <a> (idempotent).
    Returnerer True hvis noe ble endret.
    """
    spans = [s for s in a_tag.find_all("span", class_="lic", recursive=False)]
    if len(spans) < 2:
        return False

    changed = False
    for i in range(len(spans) - 1):
        left = spans[i]
        right = spans[i + 1]

        # Fjern ALT mellom venstre og høyre span
        cur = left.next_sibling
        removed_any = False
        while cur is not None and cur is not right:
            nxt = cur.next_sibling
            try:
                cur.extract()
                removed_any = True
            except Exception:
                pass
            cur = nxt

        # Normaliser "mellomrommet" rett før høyre span til *én* vanlig space
        prev = right.previous_sibling
        if isinstance(prev, NavigableString):
            if prev != " ":
                prev.replace_with(NavigableString(" "))
                changed = True
            elif removed_any:
                # Vi fjernet ting, men space var allerede korrekt – regn som endring
                changed = True
        else:
            right.insert_before(NavigableString(" "))
            changed = True

    return changed

def _iter_chapter_like_containers(soup):
    # 2.1.2
    # Prøv først kapitler/sectioner – fall tilbake til <body>
    candidates = []
    for sec in soup.find_all(["section", "article"]):
        cls = " ".join(sec.get("class", [])).lower()
        r = (sec.get("role") or "").lower()
        if any(k in cls for k in ("chapter", "kapittel", "kapittel", "del")) or r in ("doc-chapter", "chapter"):
            candidates.append(sec)
    if not candidates and soup.body:
        candidates = [soup.body]
    return candidates or [soup]  # nød-tilfelle

def _href_fragment(a):
    href = (a.get("href") or "").strip()
    if href.startswith("#") and len(href) > 1:
        return href[1:]
    return None

def _anchor_in_container(container, frag_id):
    if not frag_id:
        return False
    target = container.find(id=frag_id)
    return target is not None

def _is_backmatter_container(el) -> bool:
    et = (el.get("epub:type") or "").lower()
    if "backmatter" in et:
        return True
    role = (el.get("role") or "").lower()
    if role in ("doc-appendix", "doc-colophon", "doc-afterword", "doc-backmatter"):
        return True
    # fallback: veldig sent i dokumentet
    # (brukes bare hvis vi mangler eksplisitte markører)
    parent = el
    while parent.parent is not None:
        parent = parent.parent
    # parent er <html> eller rot — sjekk om el ligger nær slutten av <body>
    body = getattr(parent, "body", None) or parent
    try:
        blocks = [c for c in body.find_all(recursive=False)]
        if blocks and el in blocks and blocks.index(el) > int(len(blocks) * 0.6):
            return True
    except Exception:
        pass
    return False

def _epub_types(el) -> set[str]:
    """
    Returner alle epub:type-verdier som et sett med små bokstaver.

    - Tåler at el ikke er en Tag (da returneres tomt sett)
    - Manglende eller tom epub:type gir tomt sett
    - Splitt på mellomrom, semikolon og komma
    """
    if not isinstance(el, Tag):
        return set()

    raw = (el.get("epub:type") or "").strip().lower()
    if not raw:
        return set()

    # Splitt på whitespace, semikolon og komma, og fjern tomme tokens
    return {t for t in re.split(r"[\s;,]+", raw) if t}

def _get_heading_text(el):
    h = el.find(re.compile(r'^h[1-6]$', re.I)) or el.find_previous(re.compile(r'^h[1-6]$', re.I))
    return (h.get_text(" ", strip=True) if h else "").strip()

def _css_path(el):
    parts = []
    cur = el
    while getattr(cur, "name", None):
        ident = cur.name
        if cur.get("id"): ident += f"#{cur.get('id')}"
        if cur.get("class"): ident += "." + ".".join(cur.get("class"))
        parts.append(ident)
        cur = cur.parent
    return " > ".join(reversed(parts))

def _text_lines(el):
    # Del på <br> og linjeskift
    txt = el.get_text("\n", strip=True)
    return [ln.strip() for ln in re.split(r'\n+', txt) if ln.strip()]

def _snippet(el, n=140):
    t = el.get_text(" ", strip=True)
    return (t[:n] + "…") if len(t) > n else t

def _in_protected(node) -> bool:
    """
    Returner True hvis noden (eller en av dens forfedre) har et tag-navn
    som finnes i en av de globale settene:
    _PROTECTED_ANCESTORS, _PROTECTED eller PROTECTED (case-insensitivt).
    """

    # Slå sammen alle beskyttede navnesett som faktisk finnes
    protected_names: set[str] = set()
    for name in ("_PROTECTED_ANCESTORS", "_PROTECTED", "PROTECTED"):
        s = globals().get(name)
        if isinstance(s, Iterable):
            protected_names.update(str(n).lower() for n in s)

    if not protected_names:
        return False  # ingenting å sjekke mot

    p = node
    while p is not None:
        tag_name = getattr(p, "name", None)
        if tag_name and tag_name.lower() in protected_names:
            return True
        p = getattr(p, "parent", None)

    return False

def _has_alnum_text(node) -> bool:
    if isinstance(node, NavigableString):
        return bool(_ALNUM_RX.search(str(node)))
    if getattr(node, "name", None):
        return bool(_ALNUM_RX.search(node.get_text("", strip=True)))
    return False

# --- end ust used several times ------------------------------------------------------

def _collapse_adjacent_brs(parent):
    changed = 0
    for br in list(parent.find_all("br")):
        nxt = br.next_sibling
        while getattr(nxt, "name", None) == "br":
            kill = nxt
            nxt = nxt.next_sibling
            kill.decompose()
            changed += 1
    return changed

# --- Hjelpere for §2.1.12 ------------------------------------------------------

def _collect_tokens(soup):
    total_tokens = 0
    samples = []  # (token, node, context_snippet)
    for t in soup.find_all(string=True):
        if not isinstance(t, NavigableString):
            continue
        if _in_protected(t):
            continue
        s = str(t)
        # noter ikke-NFC (kun logg—ingen endring)
        if unicodedata.normalize("NFC", s) != s:
            # vi logger per node (ikke per token)
            pass
        for tok in _TOKEN_RX.findall(s):
            total_tokens += 1
            # lag små prøver for senere
            if len(samples) < 500:  # begrens prøvestørrelsen
                # lite kontekstvindu:
                ctx = s
                if len(ctx) > 160:
                    # klipp rundt forekomst
                    pos = s.find(tok)
                    start = max(0, pos - 60)
                    end = min(len(s), pos + len(tok) + 60)
                    ctx = s[start:end]
                samples.append((tok, t, ctx))
    return total_tokens, samples

def _is_suspicious_token(tok: str) -> tuple[bool, str]:
    lower = tok.lower()

    # Alfanumerisk miks som ikke er på whitelist
    if _MIX_ALNUM_RX.match(tok) and lower not in _ALLOWED_MIX:
        return True, "alpha+digit mix"

    # Klassiske OCR-mønstre rundt sifre
    for rx in _NUMERIC_MIX_OCR_RXES:
        if rx.search(tok):
            return True, "digit/letter confusion (O/I/l/S)"

    # rn→m heuristikk (svak)
    if _RN_SUSPECT_RX.search(tok):
        return True, "possible rn→m confusion"

    # Enkle “O/0/I/1/l” innesperret i motsatt miljø
    if re.search(r"[A-Za-zÆØÅæøå][01][A-Za-zÆØÅæøå]", tok):
        return True, "1/0 inside letters"
    if re.search(r"\d[OIlS]\b|\b[OIlS]\d", tok):
        return True, "letter next to digits (O/I/l/S)"

    return False, ""

# --- Hjelpere for §2.2 ------------------------------------------------------


def _first_significant_child(el):
    for c in el.children:
        # ignorer whitespace og pagebreak
        if isinstance(c, NavigableString) and not c.strip():
            continue
        if _is_pagebreak(c):
            continue
        return c
    return None

def _is_chapter_section(sec):
    et = (sec.get("epub:type") or "").lower()
    role = (sec.get("role") or "").lower()
    cls = " ".join(sec.get("class", [])).lower()
    return ("chapter" in et) or (role in ("doc-chapter", "chapter")) or ("chapter" in cls)

def _already_sectioned(h):
    sec = h.find_parent("section")
    if not sec:
        return False
    first = _first_significant_child(sec)
    return first is h

def _flatten_redundant_sections(soup, logger):
    """
    Flater ut wrapper-<section> uten attributter som kun inneholder én <section>.
    Idempotent.
    """
    removed = 0
    for outer in list(soup.find_all("section")):
        # Bevar sections som har attributter (semantikk)
        if outer.attrs:
            continue
        # Reelle barn (ignorer whitespace)
        real_children = [c for c in outer.contents
                         if not (isinstance(c, NavigableString) and not c.strip())]
        if len(real_children) == 1 and getattr(real_children[0], "name", None) == "section":
            inner = real_children[0]
            outer.replace_with(inner.extract())
            removed += 1
    if removed:
        logger.info("2.2 - Flattened %d redundant wrapper <section>(s).", removed)
    return removed

# --- Hjelpere for §2.2.1 ------------------------------------------------------

# --- Konfig / hjelpesett ------------------------------------------------------
# --- Hjelpere -----------------------------------------------------------------

def _is_task_item(el):
    return bool(_epub_types(el) & TASK_ITEM_TYPES)

def _is_task_container(el):
    return bool(_epub_types(el) & TASK_CONTAINER_TYPES)

def _has_heading_in(el):
    # “individuell oppgave har heading”: enten h1–h6, eller bridgehead brukt som oppgave-tittel
    if el.find(HEADING_RX):
        return True
    if el.find("p", attrs={"epub:type": "bridgehead"}):
        return True
    return False

def _first_heading_in(el):
    h = el.find(HEADING_RX)
    if h:
        return h
    return el.find("p", attrs={"epub:type": "bridgehead"})

# See above
'''
def _first_significant_child(el):
    for c in el.children:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        return c
    return None
'''

def _already_task_section(el):
    """
    True hvis el allerede ER en <section> med task-item-type OG første signifikante barn er en heading.
    """
    if getattr(el, "name", "").lower() != "section":
        return False
    if not (_epub_types(el) & TASK_ITEM_TYPES):
        return False
    first = _first_significant_child(el)
    if first is None:
        return False
    return bool(HEADING_RX.match(getattr(first, "name", "") or "") or
                (getattr(first, "name", "") == "p" and (first.get("epub:type") or "").lower() == "bridgehead"))

def _wrap_as_task_section(soup, node, logger):
    """
    Pakk node i <section epub:type="…"> (kopierer relevante task-typer).
    Setter aria-labelledby hvis mulig. Idempotent mot _already_task_section.
    """
    types = _epub_types(node)
    task_tokens = list((types & TASK_ITEM_TYPES) or ["assessment"])
    # Hvis node allerede er en section med task-type, ikke gjør noe
    if getattr(node, "name", "").lower() == "section" and (types & TASK_ITEM_TYPES):
        return False

    sec = soup.new_tag("section")
    sec["epub:type"] = " ".join(task_tokens)
    sec["data-auto-task-section"] = "true"

    # aria-labelledby fra første heading i node (om id finnes)
    h = _first_heading_in(node)
    if h and h.get("id"):
        sec["aria-labelledby"] = h["id"]

    node.wrap(sec)
    logger.info('2.2.1 - Wrapped task item in <section epub:type="%s">.',
                sec.get("epub:type"))
    return True

def _flatten_redundant_sections(soup, logger):
    """
    Flater ut wrapper-<section> uten attributter som kun inneholder én <section>.
    """
    removed = 0
    for outer in list(soup.find_all("section")):
        # Bevar sections som har attributter – de kan ha semantikk
        if outer.attrs:
            continue
        real_children = [c for c in outer.contents
                         if not (isinstance(c, NavigableString) and not c.strip())]
        if len(real_children) == 1 and getattr(real_children[0], "name", None) == "section":
            inner = real_children[0]
            outer.replace_with(inner.extract())
            removed += 1
    if removed:
        logger.info("2.2.1 - Flattened %d redundant wrapper <section>(s).", removed)
    return removed

# --- Hjelpere for §2.3.1 ------------------------------------------------------

def _stem_from_src(src: str) -> str:
    try:
        path = urlparse(src).path or src
        base = path.basename(path)
        stem = path.splitext(base)[0]
        return stem
    except Exception:
        return src or ""

def _tokens_for(img):
    toks = []

    # img selv
    toks += img.get("class", [])
    if img.get("id"): toks.append(img["id"])
    if img.get("aria-label"): toks.append(img["aria-label"])
    if img.get("data-type"): toks.append(img["data-type"])
    if img.get("role"): toks.append(img["role"])

    # filnavn-stem og “orddeling”
    stem = _stem_from_src(img.get("src",""))
    if stem:
        toks.append(stem)
        toks += re.split(r'[_\-\.\s]+', stem)

    # foreldre (opp til figure/section)
    p = img.parent
    hops = 0
    while p is not None and hops < 3:
        toks += p.get("class", []) or []
        if p.get("id"): toks.append(p["id"])
        if p.get("role"): toks.append(p["role"])
        if p.get("epub:type"): toks += (p.get("epub:type") or "").split()
        if p.name.lower() == "figure": toks.append("figure")
        if p.name.lower() in ("section","aside"): toks += (p.get("epub:type") or "").split()
        p = p.parent
        hops += 1

    # til én spacet streng
    label_str = " ".join(toks).lower()
    return label_str

def _looks_small_symbol(img) -> bool:
    # Små inline-ikoner – heuristikk
    try:
        w = int(img.get("width", 0))
        h = int(img.get("height", 0))
        if (w and w <= 64) or (h and h <= 64):
            return True
    except Exception:
        pass
    cls = " ".join(img.get("class", [])).lower()
    return any(k in cls for k in ("icon","symbol","glyph","emoji","bullet"))

def _classify_generic_alt(img) -> str:
    s = _tokens_for(img)

    if LOGO_RX.search(s):  return "logo"
    if MAP_RX.search(s):   return "map"
    if COMIC_RX.search(s): return "comic"
    if _looks_small_symbol(img) or ICON_RX.search(s):
        return "symbol"
    if DRAW_RX.search(s):  return "drawing"
    if PHOTO_RX.search(s): return "photo"
    if ILL_RX.search(s):   return "illustration"
    if FIG_RX.search(s):   return "figure"

    # fallback via parent <figure>
    p = img.find_parent("figure")
    if p is not None:
        return "figure"

    # siste utvei
    return "figure"


def _is_junk_alt(alt: str, src: str) -> bool:
    if alt is None:
        return True
    for rx in _JUNK_ALT_RXES:
        if rx.match(alt.strip()):
            return True
    # alt == filnavn-stem
    stem = _stem_from_src(src or "")
    if stem and alt.strip().lower() == stem.strip().lower():
        return True
    # veldig “sluggy”: nesten bare _/-/digits
    if len(alt) >= 8 and re.fullmatch(r'[-_0-9a-zA-Z]+', alt) and re.search(r'\d', alt) and not re.search(r'[A-Za-zÆØÅæøå]{3,}', alt):
        return True
    return False

# --- Hjelpere for §2.3.1 ------------------------------------------------------

def _stem_from_src(src: str) -> str:
    try:
        path = urlparse(src).path or src
        base = path.basename(path)
        stem = path.splitext(base)[0]
        return stem
    except Exception:
        return src or ""

def _tokens_for_image(img):
    toks = []
    toks += img.get("class", [])
    if img.get("id"): toks.append(img["id"])
    if img.get("role"): toks.append(img["role"])
    if img.get("aria-label"): toks.append(img["aria-label"])
    if img.get("data-type"): toks.append(img["data-type"])
    stem = _stem_from_src(img.get("src",""))
    if stem:
        toks.append(stem)
        toks += re.split(r'[_\-\.\s]+', stem)
    p = img.parent
    hops = 0
    while p is not None and hops < 3:
        toks += p.get("class", []) or []
        if p.get("id"): toks.append(p["id"])
        if p.get("role"): toks.append(p["role"])
        if p.get("epub:type"): toks += (p.get("epub:type") or "").split()
        if p.name and p.name.lower() == "figure": toks.append("figure")
        p = p.parent; hops += 1
    return " ".join(toks).lower()

def _strip_emphasis_in(el):
    for n in el.find_all(["em","strong"]):
        n.unwrap()

#LIST_LEADER_RX = re.compile(r'^\s*((\d+|[ivxlcdm]+|[a-z])[\.\)])\s+', re.I)

def _short_text(s: str) -> bool:
    if not s: return True
    if len(s) <= 80 and s.count(".") <= 1 and len(s.split()) <= 12:
        return True
    return False

def _normalize_figure_text_box(soup, box, logger):
    if box.get("data-auto-list") == "true":
        return False
    changed = False
    _strip_emphasis_in(box)
    ps = box.find_all("p", recursive=False)
    if len(ps) == 1:
        text = ps[0].get_text(" ", strip=True)
        if _short_text(text):
            ps[0].unwrap()
            changed = True
    ps = box.find_all("p", recursive=False)
    if len(ps) >= 2:
        leaders = sum(1 for p in ps if LIST_LEADER_RX.match(p.get_text(" ", strip=True)))
        if leaders >= max(2, len(ps)//2):
            ol = soup.new_tag("ol")
            for p in ps:
                t = p.get_text(" ", strip=True)
                li = soup.new_tag("li")
                t = LIST_LEADER_RX.sub("", t).strip()
                li.string = t
                ol.append(li)
                p.decompose()
            box.append(ol)
            box["data-auto-list"] = "true"
            changed = True
    if box.get("data-auto-list") != "true":
        br_parent = None
        for child in box.children:
            if getattr(child, "name", None) and child.name.lower() in {"p","div","span"}:
                if len(child.find_all("br")) >= 2:
                    br_parent = child; break
        if br_parent:
            raw, cur = [], []
            for n in br_parent.children:
                if getattr(n, "name", None) == "br":
                    raw.append("".join(t for t in cur if isinstance(t, NavigableString)).strip()); cur = []
                else:
                    cur.append(n if isinstance(n, NavigableString) else n.get_text("", strip=True))
            if cur:
                raw.append("".join(t for t in cur if isinstance(t, NavigableString)).strip())
            items = [x for x in raw if x]
            if len(items) >= 2:
                ul = soup.new_tag("ul")
                for it in items:
                    li = soup.new_tag("li"); li.string = it
                    ul.append(li)
                br_parent.replace_with(ul)
                box["data-auto-list"] = "true"
                changed = True
    return changed

# --- hva slags figurer skal IKKE ha fig-tekst ---------------------------------

def _should_never_extract_text_for(img) -> bool:
    alt = (img.get("alt") or "").strip().lower()
    toks = _tokens_for_image(img)
    # “I utgangspunktet IKKE trekk ut tekst fra”:
    if alt in {"photo","map","foto","kart"}:
        return True
    if GRAPH_RX.search(toks) or WEB_RX.search(toks) or BOOK_RX.search(toks):
        return True
    return False

# --- finn figur-tekstcontainer eller lag en -----------------------------------

def _find_or_create_fig_text_box(soup, fig):
    # typisk: <aside class="fig-desc"> rett under figure
    for cand in fig.find_all(True, recursive=False):
        if "fig-desc" in (cand.get("class") or []):
            return cand
        cls = " ".join(cand.get("class", []) or "")
        if re.search(r'\bfig(?:ure)?[-_ ]?(?:desc|text|caption)\b', cls, flags=re.I):
            return cand
    # ev. som søsken etter figure
    sib = fig.find_next_sibling()
    if sib and "fig-desc" in (sib.get("class") or []):
        return sib
    # lag en ny
    aside = soup.new_tag("aside", **{"class": "fig-desc"})
    fig.append(aside)
    return aside

def _fig_text_box_is_empty(box) -> bool:
    txt = box.get_text(" ", strip=True)
    return not bool(txt)

# --- RabbitMQ RPC (synkron, enkel) -------------------------------------------

def _rpc_ocr_image_via_rabbitmq(image_path: str, logger, *, timeout_s: float = 20.0,
                                amqp_url: str = "amqp://admin:admin@localhost:5672/%2F",
                                queue_name: str = "ocr_requests") -> str | None:
    """
    Sender en RPC-forespørsel til OCR-tjenesten via RabbitMQ.
    Forventer JSON-respons: {"text": "..."}.
    Returnerer str eller None ved feil/timeouts.
    """
    try:
        connection = pika.BlockingConnection(pika.URLParameters(amqp_url))
        channel = connection.channel()
        result = channel.queue_declare(queue="", exclusive=True, auto_delete=True)
        callback_queue = result.method.queue

        corr_id = str(uuid.uuid4())
        response_holder = {"body": None}

        def on_response(ch, method, props, body):
            if props.correlation_id == corr_id:
                response_holder["body"] = body

        channel.basic_consume(queue=callback_queue,
                              on_message_callback=on_response,
                              auto_ack=True)

        payload = {
            "action": "ocr_image_text",
            "image_path": image_path  # absolut sti på filsystemet
        }
        channel.basic_publish(
            exchange="",
            routing_key=queue_name,
            properties=pika.BasicProperties(
                reply_to=callback_queue,
                correlation_id=corr_id,
                content_type="application/json"
            ),
            body=json.dumps(payload).encode("utf-8"),
        )

        start = time.time()
        while response_holder["body"] is None and (time.time() - start) < timeout_s:
            connection.process_data_events(time_limit=0.2)

        channel.close()
        connection.close()

        if response_holder["body"] is None:
            logger.warning("2.3.2 - OCR RPC timeout for %s", image_path)
            return None

        try:
            data = json.loads(response_holder["body"].decode("utf-8"))
            text = data.get("text") or ""
            return text.strip() or None
        except Exception as e:
            logger.warning("2.3.2 - Bad OCR response for %s: %s", image_path, e)
            return None

    except Exception as e:
        logger.warning("2.3.2 - RabbitMQ OCR call failed: %s", e)
        return None

# --- resolve bildefilsti (fra src) -------------------------------------------

def _resolve_image_path(src: str, base_dir: str) -> str | None:
    if not src:
        return None
    # Dekod URL-encoding og fjern evt. leading "./"
    rel = unquote(urlparse(src).path or src).lstrip("./")
    cand = path.join(base_dir, rel)
    if path.exists(cand):
        return cand
    # Noen ganger ligger bilder i 'images/' eller liknende underkatalog
    # (her kan du legge til flere fallbacks ved behov)
    return None

# --- Hjelpere for §2.3.3 ------------------------------------------------------


def _is_fig_text_container(el) -> bool:
    if not getattr(el, "name", None):
        return False
    if el.name.lower() == "figcaption":
        return False
    cls = " ".join(el.get("class", []) or "")
    if cls and _FIGTEXT_CLASS_RX.search(cls):
        return True
    # Egenmerking fra tidligere steg
    if el.get("data-ocr") == "true":
        return True
    return False

def _next_significant_sibling(node):
    sib = node.next_sibling
    while isinstance(sib, NavigableString) and not sib.strip():
        sib = sib.next_sibling
    return sib

# --- Hjelpere for §2.3.4 ------------------------------------------------------

# --- Hjelpere for §2.3.5 ------------------------------------------------------

def _is_heading(el):
    return bool(_HEADING_RX.match(getattr(el, "name", "") or ""))

def _is_taskish(el):
    return bool(_epub_types(el) & TASK_TOKENS)

'''
def _is_other_relocated(el):
    """Noe som tidligere er flyttet (men ikke <figure>)."""
    if getattr(el, "name", "") == "figure":
        return False
    # vi bruker data-relocated* som markør i pipeline
    for k in el.attrs.keys():
        if k.startswith("data-relocated"):
            return True
    return False

'''

def _is_other_relocated(el) -> bool:
    """Noe som tidligere er flyttet (men ikke <figure>)."""
    # Vi bryr oss bare om ekte tagger
    if not isinstance(el, Tag):
        return False

    if el.name == "figure":
        return False

    # vi bruker data-relocated* som markør i pipeline
    return any(attr_name.startswith("data-relocated") for attr_name in el.attrs.keys())

def _significant_children(parent):
    """Direkte barn uten ren whitespace."""
    out = []
    for c in parent.contents:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        out.append(c)
    return out

def _in_task_ancestor(node):
    p = node.parent
    while p is not None:
        if _is_taskish(p):
            return True
        p = p.parent
    return False

# --- Hjelpere for §2.3.4 ------------------------------------------------------

def _is_pagebreak(el):
    return getattr(el, "name", "") == "div" and (el.get("epub:type") or "").lower() == "pagebreak"

def _is_chapter_section(sec):
    et = (sec.get("epub:type") or "").lower()
    role = (sec.get("role") or "").lower()
    cls = " ".join(sec.get("class", [])).lower()
    return ("chapter" in et) or (role in ("doc-chapter","chapter")) or ("chapter" in cls)

# See above
'''
def _first_significant_child(el):
    for c in el.children:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        if _is_pagebreak(c):
            # pagebreak regnes som trivielt mht “første signifikante”
            continue
        return c
    return None
'''

def _find_prev_pagebreak_sibling(node):
    sib = node.previous_sibling
    while sib is not None:
        if isinstance(sib, NavigableString) and not sib.strip():
            sib = sib.previous_sibling
            continue
        if _is_pagebreak(sib):
            return sib
        # stopper hvis vi møter en heading/figur/annet signifikant element
        sib = sib.previous_sibling
    return None

def _find_next_pagebreak_sibling(node):
    sib = node.next_sibling
    while sib is not None:
        if isinstance(sib, NavigableString) and not sib.strip():
            sib = sib.next_sibling
            continue
        if _is_pagebreak(sib):
            return sib
        sib = sib.next_sibling
    return None

def _significant_between(start_node, end_node):
    """Returner liste over direkte søsken mellom start (eksklusiv) og end (eksklusiv) som ikke bare er whitespace."""
    out = []
    sib = start_node.next_sibling
    while sib is not None and sib is not end_node:
        if not (isinstance(sib, NavigableString) and not sib.strip()):
            out.append(sib)
        sib = sib.next_sibling
    return out

def _nearest_xml_lang(node):
    p = node
    while p is not None:
        lang = p.get("xml:lang") or p.get("lang")
        if lang:
            return lang.lower()
        p = p.parent
    return None

# --- Hjelpere for §2.3.7 ------------------------------------------------------


def _is_figcaption(node) -> bool:
    return getattr(node, "name", "").lower() == "figcaption"

def _is_prodnote(node) -> bool:
    return (
        getattr(node, "name", "").lower() == "aside" and
        (node.get("epub:type") or "").lower() == "z3998:production"
    )

def _is_image_like(node) -> bool:
    return getattr(node, "name", "").lower() in {"img", "svg", "object", "embed", "picture"}

def _is_figure_text_box(node) -> bool:
    """Bokser for tekstuttrekk fra figur som skal bort i mattebøker."""
    if getattr(node, "name", "").lower() != "aside":
        return False
    cls = " ".join(node.get("class", []) or "")
    if _FIGTEXT_RX.search(cls):
        return True
    # OCR/normaliseringsmarkører fra tidligere pass
    if node.get("data-ocr") == "true":
        return True
    return False

def _has_block_descendant(node) -> bool:
    """Sjekk om node inneholder blokkelementer som antyder 'omgivende tekst/struktur'."""
    for desc in node.descendants:
        name = getattr(desc, "name", "") or ""
        if name.lower() in _BAD_BLOCKS:
            return True
    return False

# --- Hjelpere for §2.3.7.1 ------------------------------------------------------


def _tokens_for_img(img):
    toks = []
    if img.get("alt"): toks.append(img["alt"])
    if img.get("id"): toks.append(img["id"])
    toks += img.get("class", []) or []
    src = img.get("src") or ""
    if src:
        src_path = urlparse(src).path or src
        base = path.basename(src_path)
        stem = path.splitext(base)[0]
        toks.append(stem)
        toks += re.split(r'[_\-\.\s]+', stem)
    return " ".join(toks).lower()

def _figure_contains_real_table(fig):
    return bool(fig.find(["table","thead","tbody","tr","td","th"]))

def _extract_text(el):
    return (el.get_text(" ", strip=True) or "").strip()

def _ensure_table_caption_from_figcaption(table, figcaption_text):
    """Sett <caption> øverst i tabellen hvis den mangler, med tekst fra figcaption."""
    if not figcaption_text:
        return False
    has_caption = table.find("caption", recursive=False)
    if has_caption:
        return False
    cap = table.new_tag("caption")
    cap.string = figcaption_text
    # sett inn først
    table.insert(0, cap)
    return True

def _resolve_image_path(src: str, base_dir: str | None) -> str | None:
    if not src or not base_dir:
        return None
    rel = unquote(urlparse(src).path or src).lstrip("./")
    cand = path.join(base_dir, rel)
    return cand if path.exists(cand) else None

# --- Hjelpere for §2.3.8 ------------------------------------------------------


def _tokens_for_img(img):
    toks = []
    alt = (img.get("alt") or "").strip()
    if alt: toks.append(alt)
    if img.get("id"): toks.append(img["id"])
    toks += (img.get("class") or [])
    src = img.get("src") or ""
    if src:
        src_path = urlparse(src).path or src
        base = path.basename(src_path)
        stem, _ = path.splitext(base)
        toks.append(stem)
        toks += re.split(r'[_\-\.\s]+', stem)
    return " ".join(toks).lower()

def _resolve_image_path(src: str, base_dir: str | None) -> str | None:
    if not src or not base_dir:
        return None
    rel = unquote(urlparse(src).path or src).lstrip("./")
    cand = path.join(base_dir, rel)
    return cand if path.exists(cand) else None

def _find_or_create_prodnote(fig, soup):
    # Finn eksisterende prodnote (direkte barn)
    for child in fig.find_all("aside", recursive=False):
        if (child.get("epub:type") or "").lower() == "z3998:production":
            # normaliser class/innhold ved behov
            if "prodnote" not in (child.get("class") or []):
                child["class"] = ["prodnote"]
            return child, False
    # Opprett ny
    aside = soup.new_tag("aside")
    aside["class"] = ["prodnote"]
    aside["epub:type"] = "z3998:production"
    fig.append(aside)
    return aside, True

def _text_to_paragraphs(parent, soup, text: str):
    """
    Erstatter alt innhold i parent med én <p> per linje/avsnitt.
    Splitt: dobbel newline eller enkelt newline.
    """
    for c in list(parent.contents):
        c.extract()
    # grov normalisering
    s = text.replace("\r\n", "\n").strip()
    # splitt på blanklinjer først, ellers på linjeskift
    chunks = [p.strip() for p in re.split(r"\n{2,}", s) if p.strip()]
    if not chunks:
        chunks = [t.strip() for t in s.split("\n") if t.strip()]
    if not chunks:
        # fallback: enkel p
        p = soup.new_tag("p"); p.string = s
        parent.append(p)
        return 1
    count = 0
    for ch in chunks:
        p = soup.new_tag("p"); p.string = ch
        parent.append(p)
        count += 1
    return count

# --- Hjelpere for §2.4.1 ------------------------------------------------------

def _roman_to_int(s: str) -> int | None:
    m = _ROMAN_RX.match(s.upper())
    if not m:
        return None
    vals = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':200,'M':1000}
    total = 0
    prev = 0
    for ch in s.upper()[::-1]:
        v = vals[ch]
        if v < prev:
            total -= v
        else:
            total += v
            prev = v
    return total

def _strip_leading_marker(li, marker_regex: re.Pattern) -> bool:
    """
    Fjern den første nummereringsmarkøren i li (inkl punkt./parens/space) i første
    ikke-whitespace tekstnode. Returnerer True hvis noe ble fjernet.
    """
    # Finn første ikke-whitespace NavigableString i li (DFS)
    for node in li.descendants:
        if isinstance(node, NavigableString) and node.strip():
            s = str(node)
            m = marker_regex.match(s)
            if not m:
                return False
            new_text = s[m.end():]
            node.replace_with(NavigableString(new_text.lstrip()))
            return True
        # Stopp hvis vi treffer en nested <ol> før vi fant tekst – da lar vi den stå
        if getattr(node, "name", "") == "ol":
            break
    return False

def _detect_series(tokens: list[str]) -> tuple[str,int,bool] | None:
    """
    Gitt token-lista (første 'ordet' i hvert li), detekter serie:
    returner (type, start, reversed?) der type ∈ {'1','a','A','i','I'}.
    Kun aksepter hvis hele lista er konsistent sekvens.
    """
    n = len(tokens)
    if n == 0:
        return None

    # Prøv arabisk
    if all(re.match(r'^\d+$', t) for t in tokens):
        vals = [int(t) for t in tokens]
        if all(vals[i] == vals[0] + i for i in range(n)):
            return ("1", vals[0], False)
        if all(vals[i] == vals[0] - i for i in range(n)) and n > 1:
            return ("1", vals[0], True)

    # Prøv alfa lower/upper
    def alpha_seq(alpha_tokens, upper=False):
        if all(re.match(r'^[A-Z]$', t) for t in alpha_tokens) if upper else all(re.match(r'^[a-z]$', t) for t in alpha_tokens):
            vals = [(ord(t) - (65 if upper else 97) + 1) for t in alpha_tokens]
            if all(vals[i] == vals[0] + i for i in range(n)):
                return (("A" if upper else "a"), vals[0], False)
            if all(vals[i] == vals[0] - i for i in range(n)) and n > 1:
                return (("A" if upper else "a"), vals[0], True)
        return None

    r = alpha_seq(tokens, upper=False) or alpha_seq(tokens, upper=True)
    if r:
        return r

    # Prøv romertall
    romans = []
    roman_ok = True
    case = None
    for t in tokens:
        if not re.match(r'^[IVXLCDMivxlcdm]+$', t):
            roman_ok = False
            break
        val = _roman_to_int(t)
        if not val:
            roman_ok = False
            break
        romans.append(val)
        case = "I" if t and t[0].isupper() else "i"
    if roman_ok:
        if all(romans[i] == romans[0] + i for i in range(n)):
            return (case, romans[0], False)
        if all(romans[i] == romans[0] - i for i in range(n)) and n > 1:
            return (case, romans[0], True)

    return None

# --- Hjelpere for §2.4.1.1 ------------------------------------------------------

def _roman_to_int(s: str) -> int | None:
    s = s.upper()
    if not _ROMAN_VALID_RX.match(s):
        return None
    vals = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':200,'M':1000}
    total = 0
    prev = 0
    for ch in s[::-1]:
        v = vals[ch]
        if v < prev:
            total -= v
        else:
            total += v
            prev = v
    return total

def _first_text(li) -> str | None:
    """Finn første ikke-whitespace tekstnode i <li> (DFS)."""
    for node in li.descendants:
        if isinstance(node, NavigableString):
            if node.strip():
                return str(node)
        if getattr(node, "name", "") == "ol":
            # nested <ol> → ikke bland med foreldreliste
            break
    return None

def _parse_marker(tok: str) -> tuple[int, str] | None:
    """
    Tolker en enkel markør ('12', 'a', 'A', 'iv', 'IV') til (verdi, serie-type).
    type ∈ {'1','a','A','i','I'}
    """
    if tok.isdigit():
        return int(tok), '1'
    if len(tok) == 1 and 'a' <= tok <= 'z':
        return (ord(tok) - 97 + 1), 'a'
    if len(tok) == 1 and 'A' <= tok <= 'Z':
        return (ord(tok) - 65 + 1), 'A'
    if re.fullmatch(r'[ivxlcdm]+', tok):
        v = _roman_to_int(tok)
        return (v, 'i') if v else None
    if re.fullmatch(r'[IVXLCDM]+', tok):
        v = _roman_to_int(tok)
        return (v, 'I') if v else None
    return None

# --- Hjelpere for §2.4.1.2 ------------------------------------------------------

def _derive_series_from_values(lis):
    """Hvis noen <li> har @value, avled heltall-sekvens derfra (ellers None)."""
    have_any = any(li.has_attr("value") for li in lis)
    if not have_any:
        return None
    vals = []
    for li in lis:
        if li.has_attr("value"):
            try:
                vals.append(int(li["value"]))
            except Exception:
                return None
        else:
            # uten value kan vi ikke avlede kontinuerlig tall uten innhold/markør → avbryt
            return None
    # Alle har value → numerisk serie, type = '1'
    return {"values": vals, "type": "1"}

def _derive_series_from_markers(lis):
    """Les synlige markører i første tekstnode for hver li (før 2.4.1 stripper dem)."""
    tokens = []
    vals   = []
    typs   = set()
    # bred regex: tall / én bokstav / romertall (+ valgfri skilletegn + space)
    _WIDE_RX = re.compile(r'^\s*([0-9]+|[A-Za-z]|[ivxlcdmIVXLCDM]+)\s*(?:[.\)\:\-\u00A0]+)?\s+')

    # Finn første tekstbit i hver <li> (ikke dypere enn første tekstnode; stopp ved nested <ol>)
    def _first_text(li):
        for node in li.descendants:
            if isinstance(node, NavigableString):
                if node.strip():
                    return str(node)
            if getattr(node, "name", "") == "ol":
                break
        return None

    # Samme parsere som i 2.4.1.1
    def _roman_to_int(s: str):
        s2 = s.upper()
        if not re.fullmatch(r'(?=[IVXLCDM]+$)M{0,4}(CM|CD|D?C{0,3})(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})', s2):
            return None
        vals = {'I':1,'V':5,'X':10,'L':50,'C':100,'D':200,'M':1000}
        total = prev = 0
        for ch in s2[::-1]:
            v = vals[ch]
            total = total - v if v < prev else total + v
            if v >= prev: prev = v
        return total

    def _parse_marker(tok: str):
        if tok.isdigit():
            return int(tok), '1'
        if len(tok) == 1 and 'a' <= tok <= 'z':
            return (ord(tok) - 97 + 1), 'a'
        if len(tok) == 1 and 'A' <= tok <= 'Z':
            return (ord(tok) - 65 + 1), 'A'
        if re.fullmatch(r'[ivxlcdm]+', tok):
            v = _roman_to_int(tok);  return (v, 'i') if v else None
        if re.fullmatch(r'[IVXLCDM]+', tok):
            v = _roman_to_int(tok);  return (v, 'I') if v else None
        return None

    for li in lis:
        s = _first_text(li)
        if not s:
            return None
        m = _WIDE_RX.match(s)
        if not m:
            return None
        tok = m.group(1)
        parsed = _parse_marker(tok)
        if not parsed:
            return None
        v, t = parsed
        tokens.append(tok); vals.append(v); typs.add(t)

    if len(typs) != 1:
        return None
    return {"values": vals, "type": typs.pop()}

# --- Hjelpere for §2.4.1.3 ------------------------------------------------------


def _first_token(li) -> str:
    """
    Hent første 'ord' i et <li>-element slik det vil vises for leser:
    - bruk visible text (get_text(' ', strip=True)),
    - ta første 'ord' (første whitespace),
    - tillat punktum/parantes som del av markør.
    """
    text = li.get_text(" ", strip=True)
    if not text:
        return ""
    # Klipp ut første ord-sekvens (inkl evt. avsluttende . eller ))
    # Vi tar alt frem til første mellomrom.
    token = text.split(None, 1)[0]
    return token

def _looks_standard_marker(token: str) -> bool:
    if not token:
        return False
    return bool(_STD_DECIMAL_RX.match(token) or
                _STD_ALPHA_RX.match(token)   or
                _STD_ROMAN_RX.match(token))

def _looks_nonstandard_marker(token: str) -> bool:
    if not token:
        return False
    # Ikke-standard hvis den har både bokstaver og tall, eller hierarkisk 2.1.3
    if _NONSTD_ALNUM_RX.match(token):
        return True
    if _NONSTD_HIER_RX.match(token):
        return True
    return False

def _ensure_listtype_none(ol, logger):
    # class
    classes = set(ol.get("class", []))
    if "list-type-none" not in classes:
        classes.add("list-type-none")
        ol["class"] = list(classes)
    # style
    style = (ol.get("style") or "").strip()
    if "list-style-type" not in style.lower():
        new = "list-style-type: none;"
        ol["style"] = (style + (" " if style else "") + new).strip()
    elif "list-style-type: none" not in style.replace(" ", "").lower():
        # legg til/erstatt list-style-type til none
        # enkel erstatning:
        ol["style"] = re.sub(r'list-style-type\s*:\s*[^;]+', 'list-style-type: none', style, flags=re.I)

# --- Hjelpere for §2.4.1.4 ------------------------------------------------------

def _in_answer_section(node) -> bool:
    """True hvis node ligger i en svardel (section.class~key eller epub:type~answer)."""
    p = node
    while p is not None:
        name = getattr(p, "name", None)
        if name and name.lower() == "section":
            if "key" in [c.lower() for c in p.get("class", [])]:
                return True
            et = (p.get("epub:type") or "")
            if _ANSWER_RX.search(et):
                return True
        p = getattr(p, "parent", None)
    return False

def _leading_text(li) -> str:
    """Returner starttekst for <li> (flattenet), brukt for å finne 'og c)'-mønster."""
    return li.get_text(" ", strip=True) if li else ""

def _strip_conj_prefix_inplace(li) -> str | None:
    """
    Fjerner 'og X)' / 'samt X)' i starten av LI-innholdet DER DET FINNES.
    Returnerer bokstaven 'X' (som lower) hvis noe ble fjernet, ellers None.
    Bevarer øvrig markup.
    """
    if not li:
        return None
    # se på første tekstnære node
    for child in list(li.contents):
        if isinstance(child, NavigableString):
            m = _CONJ_PREFIX_RX.match(str(child))
            if m:
                letter = m.group(1).lower()
                new_text = _CONJ_PREFIX_RX.sub("", str(child), count=1)
                if new_text:
                    child.replace_with(NavigableString(new_text))
                else:
                    child.extract()
                return letter
            # hvis første node er tekst men uten match, stopp – da finnes ikke prefikset helt foran
            return None
        elif getattr(child, "name", None):
            # første node er et element (f.eks. table); da kan ikke "og c)" stå helt i starten
            return None
    return None

def _append_with_space(tag, what):
    """Append with a single space separator if needed."""
    if not tag.contents:
        tag.append(what)
        return
    last = tag.contents[-1]
    need_space = True
    if isinstance(last, NavigableString):
        if str(last).endswith((" ", "\u00A0")):
            need_space = False
    if need_space:
        tag.append(NavigableString(" "))
    tag.append(what)

def _alpha_start(ol) -> int:
    try:
        return int(ol.get("start", "1"))
    except Exception:
        return 1

# --- Hjelpere for §2.4.2 ------------------------------------------------------

def _strip_text_bullet_prefix_inplace(li) -> bool:
    """Fjern kuletegn i starten av LI når de ligger som ren tekst. Returnerer True hvis noe ble fjernet."""
    changed = False
    # Gå gjennom første par noder for å plukke opp tekstprefix
    for child in list(li.contents):
        # Hopp over tomt whitespace først
        if isinstance(child, NavigableString) and not child.strip():
            continue
        if isinstance(child, NavigableString):
            m = _BULLET_PREFIX_RX.match(str(child))
            if m:
                new_text = _BULLET_PREFIX_RX.sub("", str(child), count=1)
                if new_text:
                    child.replace_with(NavigableString(new_text))
                else:
                    child.extract()
                changed = True
            break
        # Første node er et element – da kan kula ligge i et <span> e.l.
        break
    return changed

def _strip_element_bullet_prefix_inplace(li) -> bool:
    """
    Fjern kuletegn når de ligger i eget element helt først (f.eks. <span>—</span>&nbsp;Tekst).
    Vi fjerner elementer som bare består av kuletegn/whitespace.
    """
    changed = False
    # Iterér fra starten og fjern "kule-elementer" og påfølgende whitespace
    while li.contents:
        first = li.contents[0]
        # 1) tomt whitespace
        if isinstance(first, NavigableString) and not first.strip():
            first.extract(); changed = True; continue
        # 2) rent tekst-kuleelement
        if isinstance(first, NavigableString):
            m = _BULLET_PREFIX_RX.match(str(first))
            if m:
                new_text = _BULLET_PREFIX_RX.sub("", str(first), count=1)
                if new_text:
                    first.replace_with(NavigableString(new_text))
                else:
                    first.extract()
                changed = True
            break
        # 3) element som bare inneholder kuletegn/whitespace
        if getattr(first, "name", None):
            txt = first.get_text("", strip=True)
            if txt and all(ch in _BULLET_CHARS for ch in txt):
                first.extract(); changed = True; continue
        # ellers: første “reelle” innhold – stopp
        break
    return changed

def _normalize_plain_ul(ul) -> bool:
    """
    Sørg for class=list-unstyled når lista er ment å være uten kuler.
    Returnerer True hvis noe ble endret.
    """
    changed = False
    # normaliser class
    classes = set(ul.get("class", []))
    if "list-unstyled" not in classes:
        if classes & _PLAIN_CLASSES or _LST_NONE_RX.search((ul.get("style") or "")):
            classes |= {"list-unstyled"}
            ul["class"] = list(classes)
            changed = True
    # fjern list-style-type:none fra style (vi bruker klassen i stedet)
    style = (ul.get("style") or "")
    if _LST_NONE_RX.search(style):
        new_style = re.sub(r'list-style-type\s*:\s*none\s*;?', "", style, flags=re.I).strip()
        # rydde opp doble semikolon/mellomrom
        new_style = re.sub(r'\s*;\s*;', ';', new_style)
        if new_style:
            ul["style"] = new_style
        elif "style" in ul.attrs:
            del ul["style"]
        changed = True
    return changed

# --- Hjelpere for §2.4.3 ------------------------------------------------------

def _has_block_children(li) -> bool:
    for child in li.find_all(recursive=False):
        name = getattr(child, "name", "") or ""
        if name.lower() in _BLOCKY:
            return True
    return False

def _prev_non_ws_sibling(node):
    sib = node.previous_sibling
    while isinstance(sib, NavigableString) and not sib.strip():
        sib = sib.previous_sibling
    return sib

# --- Hjelpere for §2.4.4 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _nearest_heading_level(node) -> int | None:
    """
    Finn et fornuftig heading-nivå for en ny tittel:
    - Ser etter nærmeste heading i samme container eller oppover
    - Returnerer nivå+1 (maks 6). Hvis ingen funnet → 3.
    """
    # 1) Sjekk foregående søsken i samme forelder
    p = node.parent
    if p:
        cur = node.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling

    # 2) Se oppover: finn første heading i samme forfader-blokk
    anc = node.parent
    while anc is not None:
        # heading som direkte barn i denne anc?
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent

    # Fallback
    return 3

def _ensure_dt_colon_space(dt) -> bool:
    """
    Legg til ': ' på slutten av <dt> dersom det ikke allerede finnes.
    Bevar eventuell markup inni <dt>.
    """
    # Finn siste synlige node i dt
    last = None
    for c in dt.contents[::-1]:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        last = c
        break

    if last is None:
        # tom dt → sett bare ': '
        dt.append(NavigableString(": "))
        return True

    if isinstance(last, NavigableString):
        s = str(last)
        # Fjern trailing whitespace; vi normaliserer til ': ' uansett
        s_stripped = s.rstrip()
        if s_stripped.endswith(":"):
            # sørg for nøyaktig ett space etter colon
            if not s.endswith(": "):
                last.replace_with(NavigableString(s_stripped + ": "))
                return True
            return False
        else:
            # legg til ': '
            last.replace_with(NavigableString(s + ": "))
            return True
    else:
        # Siste node er et element → sett tekstnode ': ' etter den
        dt.append(NavigableString(": "))
        return True

# --- Hjelpere for §2.4.4.1 ------------------------------------------------------

# ——— Hjelpere for å iterere parvis i <dl> ———
def _iter_dt_dd_pairs(dl):
    cur_dt = None
    cur_dds = []
    for child in dl.children:
        name = getattr(child, "name", None)
        if not name:
            continue
        if name.lower() == "dt":
            if cur_dt is not None:
                yield cur_dt, cur_dds
            cur_dt = child
            cur_dds = []
        elif name.lower() == "dd" and cur_dt is not None:
            cur_dds.append(child)
    if cur_dt is not None:
        yield cur_dt, cur_dds

def _text_view(tag) -> str:
    return tag.get_text(" ", strip=True)

# ——— IPA-nytte ———
def _first_ipa_in(tag):
    """Returner (fullmatch_str, inner_payload) for første IPA i tag, eller None."""
    # Søk slash først (mest vanlig i spesifikasjonen)
    for text in tag.find_all(string=True):
        s = str(text)
        m = _IPA_SLASH_RX.search(s)
        if m:
            return m.group(0), m.group(1)
        m2 = _IPA_BRACK_RX.search(s)
        if m2:
            return m2.group(0), m2.group(1)
    return None

def _normalize_ipa_payload(payload: str) -> str:
    """Komprimer whitespace/linjeskift i IPA til ingenting (typisk), behold diakritika/stress."""
    # Fjern alt whitespace inne i IPA
    compact = re.sub(r"\s+", "", payload)
    return compact

def _remove_first_literal_occurrence(tag, literal: str) -> bool:
    """Fjern første forekomst av den eksakte strengen `literal` i tekstnoder under `tag`."""
    for text in tag.find_all(string=True):
        s = str(text)
        idx = s.find(literal)
        if idx != -1:
            new = s[:idx] + s[idx + len(literal):]
            text.replace_with(new)
            return True
    return False

def _ensure_dt_colon_space_inplace(dt) -> None:
    """Sørg for at dt ender med ': ' (samme logikk som i §2.4.4)."""
    # Finn siste synlige node
    last = None
    for c in dt.contents[::-1]:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        last = c
        break
    if last is None:
        dt.append(NavigableString(": "))
        return
    if isinstance(last, NavigableString):
        s = str(last)
        if s.endswith(": "):
            return
        if s.endswith(":"):
            last.replace_with(s + " ")
        else:
            dt.append(NavigableString(": "))
    else:
        dt.append(NavigableString(": "))

def _insert_ipa_before_trailing_colon(dt, ipa_slash: str) -> bool:
    """
    Sett inn ' /ipa/ ' rett før den avsluttende kolon i dt hvis en slik kolon finnes,
    ellers append på slutten. Returnerer True hvis noe ble satt inn.
    """
    # Finn siste tekstnode
    last_text = None
    last_idx = None
    for i in range(len(dt.contents)-1, -1, -1):
        node = dt.contents[i]
        if isinstance(node, NavigableString):
            last_text = node
            last_idx = i
            break

    ipa_with_space = " " + ipa_slash
    if last_text is not None:
        s = str(last_text)
        if s.endswith(": ") or s.endswith(":"):
            # Sett IPA rett før kolon
            without_colon = s[:-1] if s.endswith(":") else s[:-2]
            # Behold trailing space/colon etterpå
            trail = s[-1:] if s.endswith(":") else ": "
            last_text.replace_with(without_colon + ipa_with_space + trail)
            return True
        else:
            # ingen trailing kolon i siste tekstnode – bare legg til IPA etter denne noden
            last_text.replace_with(s + ipa_with_space)
            return True
    else:
        # dt slutter på element – appender
        dt.append(NavigableString(ipa_with_space))
        return True

# --- Hjelpere for §2.4.4.2 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _nearest_heading_level(node: Tag) -> int:
    # Sjekk forrige søsken
    p = node.parent
    if p:
        cur = node.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling
    # Søk oppover etter nærmeste heading
    anc = node.parent
    while anc is not None:
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 3

def _tokenize_types(val: str) -> set[str]:
    return set((val or "").lower().replace(";", " ").replace(",", " ").split())

def _is_task_tag(tag: Tag) -> bool:
    et = _tokenize_types(tag.get("epub:type", ""))
    return bool(_TASK_TOKENS & et)

def _is_box_aside(aside: Tag) -> bool:
    """Heuristikk: en 'boks' har annet vesentlig innhold i tillegg til dl (tekst, figurer, lister)."""
    if aside.name != "aside":
        return False
    # prodnote/fig-desc skal ikke behandles som 'boks'
    classes = set(aside.get("class", []))
    et = (aside.get("epub:type") or "").lower()
    if "prodnote" in classes or et == "z3998:production" or "fig-desc" in classes:
        return False
    # Har asiden kun dl (+ ev. overskrift)? Da er den ikke 'boks'
    has_non_dl = False
    for child in aside.find_all(recursive=False):
        n = getattr(child, "name", "") or ""
        if _HEADING_RX.match(n) or n == "dl":
            continue
        has_non_dl = True
        break
    return has_non_dl

def _dl_in_relocated_container(dl: Tag) -> bool:
    anc = dl
    while anc is not None:
        if getattr(anc, "name", None) == "aside" and anc.get("data-relocated") == "dl-glossary":
            return True
        anc = anc.parent
    return False

def _nearest_section(tag: Tag, soup) -> Tag | None:
    anc = tag
    while anc is not None:
        if getattr(anc, "name", None) == "section":
            return anc
        anc = anc.parent
    return soup.body or soup

def _find_prev_page_number(node: Tag) -> str | None:
    """Finn nærmeste tidligere pagebreak og hent sidetall (aria-label|title|id)."""
    for el in node.previous_elements:
        if isinstance(el, Tag):
            et = _tokenize_types(el.get("epub:type", ""))
            if "pagebreak" in et:
                label = el.get("aria-label") or el.get("title") or el.get("id") or ""
                # plukk ut første tallsekvens
                m = re.search(r'\d+', label)
                return m.group(0) if m else (label.strip() or None)
    return None

def _find_insertion_point(section: Tag) -> Tag | None:
    """
    Plasser etter bilder/andre aside, men før tasks.
    - Finn første task på toppnivå → insert før denne.
    - Ellers finn siste (figure/aside) → insert etter denne.
    - Ellers → på slutten (returner None, så bruker vi append).
    """
    children = [c for c in section.children if isinstance(c, Tag)]
    first_task_idx = None
    last_media_idx = None
    for idx, c in enumerate(children):
        if _is_task_tag(c):
            first_task_idx = idx
            break
        if c.name in {"figure", "aside"}:
            last_media_idx = idx
    if first_task_idx is not None:
        return children[first_task_idx]
    if last_media_idx is not None:
        return children[last_media_idx].next_sibling  # insert after
    return None  # append at end

def _ensure_glossary_container(soup, section: Tag, lang: str) -> tuple[Tag, int]:
    """Sikre/lag <aside class="glossary" data-relocated="dl-glossary"> med hovedoverskrift."""
    container = section.find("aside", recursive=False, attrs={"data-relocated": "dl-glossary"})
    if container:
        # Finn hovedoverskriftsnivå
        for child in container.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return container, int(m.group(1))
        # Hvis ingen, beregn et nivå nå
        level = _nearest_heading_level(section)
        return container, level
    # Lag ny
    container = soup.new_tag("aside")
    container["class"] = ["glossary"]
    container["data-relocated"] = "dl-glossary"
    # Hovedoverskrift
    level = _nearest_heading_level(section)
    main_h = soup.new_tag(f"h{level}")
    title = {"en": "Glossary"}.get(lang, "Ordforklaringer")
    main_h.string = title
    container.append(main_h)
    # Sett inn container på riktig sted
    ref = _find_insertion_point(section)
    if ref is None:
        section.append(container)
    else:
        # ref kan være en sibling-pek (evt. None) – håndter begge
        if isinstance(ref, Tag) and ref.parent is section:
            ref.insert_before(container)
        else:
            section.append(container)
    return container, level

def _ensure_page_group(soup, container: Tag, page_label: str, sub_level: int, lang: str) -> Tag:
    """Sikre underoverskrift h(sub_level+1) 'Side N'/'Page N:' og en <dl data-page='N'> like etter."""
    # Sjekk om vi allerede har en gruppe for denne siden
    dl_page = None
    for dl in container.find_all("dl", recursive=False):
        if dl.get("data-page") == page_label:
            return dl
    # Finn etter hovedoverskrift – vi legger grupper fortløpende
    sub_h = soup.new_tag(f"h{min(sub_level+1, 6)}")
    if lang == "en":
        sub_h.string = f"Page {page_label}:"
    else:
        sub_h.string = f"Side {page_label}"
    container.append(sub_h)
    dl_page = soup.new_tag("dl")
    dl_page["data-page"] = page_label
    container.append(dl_page)
    return dl_page

# --- Hjelpere for §2.5.1.1 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _task_title_for_lang(lang: str) -> str:
    if lang.startswith("en"):
        return "Tasks"
    if lang.startswith("nn"):
        return "Oppgåver"
    # nb/no/annet
    return "Oppgaver"

def _has_heading(sec: Tag) -> bool:
    # heading som direkte barn, eller bridgehead som første nyttige node
    for c in sec.find_all(recursive=False):
        if isinstance(c, NavigableString) and not c.strip():
            continue
        if getattr(c, "name", "") and (_HEADING_RX.match(c.name) or
                                       (c.name == "p" and (c.get("epub:type") or "").lower() == "bridgehead")):
            return True
        return False
    return False

def _nearest_heading_level(node: Tag) -> int:
    # se nærmeste heading i samme blokk → +1 (maks 6)
    p = node.parent
    if p:
        cur = node.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling
    anc = node.parent
    while anc is not None:
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 3

def _is_answer_context(el: Tag) -> bool:
    for anc in el.parents:
        if getattr(anc, "name", None) == "section":
            if "key" in (anc.get("class") or []):
                return True
            if _epub_types(anc) & _ANSWER_TOKENS:
                return True
    return False

def _count_immediate_task_children(sec: Tag) -> int:
    """Teller 'task-aktige' direkte barn (seksjoner merket task eller elementer med task-tokens)."""
    n = 0
    for c in sec.find_all(recursive=False):
        if not isinstance(c, Tag):
            continue
        if ("task" in (c.get("class") or [])) or (_epub_types(c) & _TASK_TOKENS):
            n += 1
    return n


# --- Hjelpere for §2.5.1.2 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _task_label_for_lang(lang: str) -> str:
    if lang.startswith("en"):
        return "Task"
    if lang.startswith("nn"):
        return "Oppgåve"
    return "Oppgave"

def _is_answer_context(el: Tag) -> bool:
    for anc in el.parents:
        if getattr(anc, "name", None) == "section":
            if "key" in (anc.get("class") or []):
                return True
            if _epub_types(anc) & _ANSWER_TOKENS:
                return True
    return False

def _nearest_heading_level(node: Tag) -> int:
    p = node.parent
    if p:
        cur = node.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling
    anc = node.parent
    while anc is not None:
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 4  # litt lavere enn gruppeoverskrifter

def _first_sig_child(el: Tag):
    for c in el.children:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        return c
    return None

def _li_has_heading(li: Tag) -> bool:
    first = _first_sig_child(li)
    return bool(first and getattr(first, "name", "") and _HEADING_RX.match(first.name))

def _p_is_textual_heading(p: Tag) -> bool:
    # Fanger "Oppgave 1" / "Oppgåve 1" / "Task 1" først i <p>
    t = (p.get_text(" ", strip=True) or "").strip()
    return bool(re.match(r"^(Oppgave|Oppgåve|Task)\s+\S+", t, flags=re.I))

def _compute_decimal_number_for_li(li: Tag) -> int | None:
    """
    Beregn vist nummer for <li> i en <ol> med type '1' (eller uten type).
    Tar hensyn til <ol start> og li[value].
    Returnerer None for <ul> eller ikke-desimal <ol>.
    """
    ol = li.find_parent("ol")
    if not ol:
        return None
    t = (ol.get("type") or "1").lower()
    if t not in {"1", ""}:
        # alpha/roman – spes sier tall i heading, men vi holder oss til desimal der det gir mening
        # Du kan utvide hvis du vil mappe roman/alfa til tall.
        pass

    # start-verdi
    try:
        start = int(ol.get("start", "1"))
    except Exception:
        start = 1

    # iterer søsken for å finne reell pos og håndter value-overstyring
    n = start - 1
    for sib in ol.find_all("li", recursive=False):
        # bump baseline
        n += 1
        if sib is li:
            # hvis denne LI har 'value', bruk den
            if sib.has_attr("value"):
                try:
                    return int(sib["value"])
                except Exception:
                    return n
            return n
        else:
            # juster løpende hvis tidligere li har value
            if sib.has_attr("value"):
                try:
                    n = int(sib["value"])
                except Exception:
                    # behold n
                    pass

    return None

def _is_complex_li(li: Tag) -> bool:
    # 1) blokk-elementer?
    for child in li.find_all(recursive=False):
        name = getattr(child, "name", "") or ""
        if name in _BLOCKY:
            return True
    # 2) nestede lister?
    if li.find(["ul", "ol"]):
        return True
    # 3) flere avsnitt?
    ps = li.find_all("p", recursive=False)
    if len(ps) >= 2:
        return True
    # 4) lang tekst (heuristikk)
    txt = (li.get_text(" ", strip=True) or "")
    if len(txt) > 180:
        return True
    return False

def _convert_p_to_heading(p: Tag, level: int):
    p.name = f"h{min(max(level,1),6)}"

def _ensure_heading_in_li(soup, li: Tag, level: int, label: str, number: int | None, logger) -> bool:
    """
    Sett inn (eller konverter) heading som første barn i LI.
    Returnerer True hvis noe ble endret.
    """
    first = _first_sig_child(li)

    # a) Allerede en heading først? La stå.
    if first is not None and getattr(first, "name", "") and _HEADING_RX.match(first.name):
        return False

    # b) Første <p> ser ut som "Oppgave 1 ..." → konverter p til heading (unngå duplisering)
    if first is not None and getattr(first, "name", "") == "p" and _p_is_textual_heading(first):
        _convert_p_to_heading(first, level)
        return True

    # c) Sett inn ny heading
    text_n = f"{label}"
    if number is not None:
        text_n += f" {number}"
    h = soup.new_tag(f"h{min(max(level,1),6)}")
    h.string = text_n
    if first is None:
        li.append(h)
    else:
        first.insert_before(h)
    return True

# --- Hjelpere for §2.5.1.3 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _task_label_for_lang(lang: str) -> str:
    if lang.startswith("en"):
        return "Task"
    if lang.startswith("nn"):
        return "Oppgåve"
    return "Oppgave"

def _is_answer_context(el: Tag) -> bool:
    for anc in el.parents:
        if getattr(anc, "name", None) == "section":
            if "key" in (anc.get("class") or []):
                return True
            if _epub_types(anc) & _ANSWER_TOKENS:
                return True
    return False

def _nearest_heading_level(node: Tag) -> int:
    p = node.parent
    if p:
        cur = node.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling
    anc = node.parent
    while anc is not None:
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 4

def _first_sig_child(el: Tag):
    for c in el.children:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        return c
    return None

def _p_is_textual_heading(p: Tag) -> bool:
    t = (p.get_text(" ", strip=True) or "").strip()
    return bool(re.match(r"^(Oppgave|Oppgåve|Task)\s+\S+", t, flags=re.I))

def _is_complex_li(li: Tag) -> bool:
    for child in li.find_all(recursive=False):
        name = getattr(child, "name", "") or ""
        if name in _BLOCKY:
            return True
    if li.find(["ul", "ol"]):
        return True
    if len(li.find_all("p", recursive=False)) >= 2:
        return True
    txt = (li.get_text(" ", strip=True) or "")
    if len(txt) > 180:
        return True
    return False

def _compute_decimal_number_for_li(li: Tag) -> int | None:
    ol = li.find_parent("ol")
    if not ol:
        return None
    t = (ol.get("type") or "1").lower()
    # Vi bruker desimalnummer for overskrift – uavhengig av ol-type (vanlig i oppgaver)
    try:
        start = int(ol.get("start", "1"))
    except Exception:
        start = 1
    n = start - 1
    for sib in ol.find_all("li", recursive=False):
        n += 1
        if sib is li:
            if sib.has_attr("value"):
                try:
                    return int(sib["value"])
                except Exception:
                    return n
            return n
        else:
            if sib.has_attr("value"):
                try:
                    n = int(sib["value"])
                except Exception:
                    pass
    return None

def _alpha_index_to_letters(idx: int) -> str:
    """1 -> a, 2 -> b, ... 26 -> z, 27 -> aa, 28 -> ab, ..."""
    res = []
    i = max(1, idx)
    while i > 0:
        i -= 1
        res.append(chr(ord('a') + (i % 26)))
        i //= 26
    return "".join(reversed(res))

def _compute_alpha_letter_for_li(li: Tag) -> str | None:
    """Returner bokstav for li i <ol type='a'|'A'> med hensyn til start og li[value]."""
    ol = li.find_parent("ol")
    if not ol:
        return None
    t = (ol.get("type") or "").lower()
    if t not in {"a", ""}:
        # Hvis ol type ikke er alfabetisk, prøv å lese eksplisitt bokstav i teksten ("a)", "b.", "c ")
        token = (li.get_text(" ", strip=True) or "").split(None, 1)[0]
        m = re.match(r"([A-Za-z])[.)]?$", token)
        if m:
            return m.group(1).lower()
        return None
    # alfabetisk liste
    try:
        start = int(ol.get("start", "1"))
    except Exception:
        start = 1
    # finn indeks m/ value
    idx = start - 1
    for sib in ol.find_all("li", recursive=False):
        idx += 1
        if sib is li:
            if sib.has_attr("value"):
                try:
                    v = int(sib["value"])
                    return _alpha_index_to_letters(v).lower()
                except Exception:
                    return _alpha_index_to_letters(idx).lower()
            return _alpha_index_to_letters(idx).lower()
        else:
            if sib.has_attr("value"):
                try:
                    idx = int(sib["value"])
                except Exception:
                    pass
    return None

# --- Hjelpere for §2.5.1.3 ------------------------------------------------------

def _is_answer_context(el: Tag) -> bool:
    # Sjekk oppover etter section med class="key" eller epub:type ~ answer
    for anc in el.parents:
        if getattr(anc, "name", None) == "section":
            if "key" in (anc.get("class") or []):
                return True
            if _epub_types(anc) & _ANSWER_TOKENS:
                return True
    return False

def _find_first_heading(el: Tag) -> Tag | None:
    # Første betydningsfulle barn som er en heading
    for c in el.children:
        if isinstance(c, NavigableString):
            if not c.strip():
                continue
            # tekst – ikke en heading
            return None
        if isinstance(c, Tag):
            if _HEADING_RX.match(c.name or ""):
                return c
            # hvis første element ikke er heading, gir vi opp (vi krever “individuell heading”)
            return None
    return None

def _add_class(tag: Tag, value: str):
    cls = set(tag.get("class", []) or [])
    if value not in cls:
        cls.add(value)
        tag["class"] = list(cls)

def _drop_class(tag: Tag, value: str):
    cls = set(tag.get("class", []) or [])
    if value in cls:
        cls.remove(value)
        if cls:
            tag["class"] = list(cls)
        elif "class" in tag.attrs:
            del tag["class"]

def _ensure_aria_labelledby(section: Tag, heading: Tag):
    hid = heading.get("id")
    if hid and section.get("aria-labelledby") != hid:
        section["aria-labelledby"] = hid

# --- Hjelpere for §2.5.1.3 ------------------------------------------------------

def _in_task_context(el: Tag) -> bool:
    """Er noden inne i en task-seksjon / task-type epub:type?"""
    p = el
    while p is not None:
        if getattr(p, "name", None) in {"section", "article", "div", "li"}:
            cls = set(p.get("class", []) or [])
            if "task" in cls:
                return True
            if _epub_types(p) & _TASK_TOKENS:
                return True
        p = p.parent
    return False

def _is_likely_symbol(img: Tag) -> bool:
    """Konservativ heuristikk for å unngå vanlige bilder."""
    if img.find_parent("figure"):
        return False  # ikke rør figurer
    # små dimensjoner, klassene 'icon'/'symbol', i heading, eller tidlig i et li/p
    w = h = None
    try:
        w = int(re.sub(r"[^\d]", "", img.get("width", "") or ""))
    except Exception:
        pass
    try:
        h = int(re.sub(r"[^\d]", "", img.get("height", "") or ""))
    except Exception:
        pass
    small = (w and w <= 64) or (h and h <= 64)

    cls = {c.lower() for c in (img.get("class") or [])}
    has_icon_class = bool({"icon", "symbol", "task-icon", "oppgavesymbol"} & cls)

    in_heading = False
    p = img.parent
    while p is not None:
        n = getattr(p, "name", "") or ""
        if re.fullmatch(r"h[1-6]", n or "", flags=re.I):
            in_heading = True
            break
        # stopp hvis vi går for langt
        if n in {"li", "p", "section", "article"}:
            break
        p = p.parent

    # først barn i <li> eller i første <p> under <li>
    early_inline = False
    li = img.find_parent("li")
    if li:
        # er img første betydningsfulle node?
        for c in li.contents:
            if isinstance(c, NavigableString) and not c.strip():
                continue
            if c is img:
                early_inline = True
            break
        if not early_inline:
            # sjekk første p i li
            p0 = li.find("p", recursive=False)
            if p0 and img in p0.contents[:3]:  # veldig tidlig i første p
                early_inline = True

    return in_heading or has_icon_class or (small and early_inline)

def _basename_noext(src: str) -> str:
    base = path.basename(src or "")
    return path.splitext(base)[0].lower()

def _load_task_symbol_map(folders, logger):
    """
    Forsøker å laste en JSON-mapping fra f.eks. static/task_symbol_map.json:
    {
      "icon_write": "Skriv",
      "icon_discuss": "Samtale",
      "calculate": "Regn",
      "…": "…"
    }
    Nøkler matches mot filnavn U/T filending og mot alt-tekst (lower).
    """
    import json
    paths = []
    if folders and "static" in folders:
        paths.append(path.join(folders["static"], "task_symbol_map.json"))
    paths.append("task_symbol_map.json")  # fallback i cwd

    for p in paths:
        try:
            if path.exists(p):
                with open(p, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    if isinstance(data, dict):
                        logger.info(f"2.5.1.5 - Loaded symbol map from {p}")
                        # normaliser til lower
                        return {str(k).lower(): str(v) for k, v in data.items()}
        except Exception as e:
            logger.warning(f"2.5.1.5 - Failed loading symbol map {p}: {e}")
    return {}

def _classify_with_llm_stub(img: Tag, logger):
    """
    Dummy LLM-hook: returner None (ingen klassifisering).
    I din integrasjon kan du publisere en jobb til RabbitMQ og få tilbake label.
    """
    return None

def _resolve_task_label(img: Tag, symbol_map: dict, use_llm: bool, logger) -> str | None:
    # 1) eksplisitt data-task-type på img/forelder
    for node in (img, img.parent, img.find_parent("figure")):
        if not isinstance(node, Tag):
            continue
        val = node.get("data-task-type")
        if isinstance(val, str) and val.strip():
            return val.strip()

    # 2) via mapping: basenavn på src
    src = img.get("src") or ""
    if src:
        key = _basename_noext(src)
        if key in symbol_map:
            return symbol_map[key]

    # 3) via mapping: alt-tekst
    alt = (img.get("alt") or "").strip()
    if alt:
        alt_l = alt.lower()
        if alt_l not in _GENERIC_ALT and alt_l in symbol_map:
            return symbol_map[alt_l]
        # hvis alt ser allerede ut som en rimelig term (inneholder bokstaver og ikke bare "symbol")
        if alt_l not in _GENERIC_ALT and re.search(r"[a-zæøå]", alt_l):
            return alt.strip()

    # 4) (valgfritt) LLM
    if use_llm:
        label = _classify_with_llm_stub(img, logger)
        if label:
            return label

    return None

def _already_replaced(img: Tag) -> bool:
    # Har vi en kommentar rett etter som starter med 'symbol:' eller en span.task-type akkurat der?
    nxt = img.next_sibling
    if isinstance(nxt, Comment) and str(nxt).strip().startswith("symbol:"):
        return True
    # Sjekk om img allerede er fjernet men vi ser en span/task-type – ikke relevant her.
    return False

# --- Hjelpere for §2.5.1.6 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _list_title(i: int, lang: str) -> str:
    # i: 1 eller 2
    if lang.startswith("en"):
        return f"List {i}"
    return f"Liste {i}"

def _ensure_list_title_before(lst: Tag, title_text: str) -> bool:
    """
    Sørg for <p><strong>title</strong></p> rett foran lista.
    Returnerer True hvis noe ble endret.
    """
    # Sjekk nærmeste forrige søsken som ikke er tom-whitespace
    prev = lst.previous_sibling
    while isinstance(prev, NavigableString) and not prev.strip():
        prev = prev.previous_sibling

    if isinstance(prev, Tag) and prev.name == "p":
        # finnes <strong>…</strong> med samme tittel?
        st = prev.find("strong", recursive=False)
        if st and (st.get_text("", strip=True) == title_text) and prev.get_text("", strip=True) == title_text:
            return False  # allerede ok

    p = lst.new_tag("p")
    strong = lst.new_tag("strong")
    strong.string = title_text
    p.append(strong)
    lst.insert_before(p)
    return True

def _normalize_ul_plain(lst: Tag) -> bool:
    """
    Hvis ul er kuleløs (style list-style-type:none eller class=plain/list-style-type-none),
    normaliser til class='list-unstyled' og fjern inline style.
    """
    if lst.name != "ul":
        return False
    changed = False
    cls = set(lst.get("class", []) or [])
    style = (lst.get("style") or "").strip().lower()
    if ("plain" in cls) or ("list-style-type-none" in cls) or ("list-unstyled" in cls) or ("list-style: none" in style) or ("list-style-type:none" in style):
        if "list-unstyled" not in cls:
            cls.add("list-unstyled")
            lst["class"] = list(cls); changed = True
        if "style" in lst.attrs:
            # fjern bare list-style-type:none; bevar ev. annet
            new_style = re.sub(r"(?:^|;)\s*list-style-type\s*:\s*none\s*;?", "", (lst.get("style") or ""), flags=re.I).strip()
            if new_style:
                lst["style"] = new_style
            else:
                del lst["style"]
            changed = True
    return changed

def _extract_cell_contents_to_li(tag, new_li_parent: Tag):
    """Flytt *innholdet* (ikke <td> selv) inn i nytt <li>."""
    li = new_li_parent.new_tag("li")
    # flytt alt innhold
    for node in list(tag.contents):
        li.append(node.extract())
    new_li_parent.append(li)

def _convert_table_to_two_lists(tbl: Tag, soup, lang: str, logger) -> tuple[Tag, Tag] | None:
    """
    Konverter en tabell med to kolonner til to parallelle lister.
    Returnerer (left_list, right_list) eller None hvis ikke anvendelig.
    """
    # Very conservative: eksakt 2 kolonner i alle rader
    rows = tbl.find_all("tr")
    if not rows:
        return None
    # sjekk kolonneantall (ignorer thead/tfoot – vi tar bare tbody/tr)
    body_rows = [r for r in rows if r.find_parent("tbody") or (not r.find_parent("thead") and not r.find_parent("tfoot"))]
    if not body_rows:
        body_rows = rows
    # Bruk første rad som mål
    first_tds = body_rows[0].find_all(["td", "th"], recursive=False)
    if len(first_tds) != 2:
        return None
    for r in body_rows:
        if len(r.find_all(["td", "th"], recursive=False)) != 2:
            return None

    # Ok – lag to lister (ul class='list-unstyled' til vi evt. vil nummerere)
    left_ul  = soup.new_tag("ul");  left_ul["class"]  = ["list-unstyled"]
    right_ul = soup.new_tag("ul");  right_ul["class"] = ["list-unstyled"]

    # Titteler (settes etterpå, idempotent logikk sørger for ikke å duplisere)
    # Plasser lister der tabellen stod
    tbl.insert_before(left_ul)
    tbl.insert_before(right_ul)
    for r in body_rows:
        cells = r.find_all(["td", "th"], recursive=False)
        _extract_cell_contents_to_li(cells[0], left_ul)
        _extract_cell_contents_to_li(cells[1], right_ul)

    # Fjern tabellen
    tbl.decompose()

    # sett titler
    _ensure_list_title_before(left_ul,  _list_title(1, lang))
    _ensure_list_title_before(right_ul, _list_title(2, lang))

    return left_ul, right_ul

# --- Hjelpere for §2.5.1.7 ------------------------------------------------------


def _in_fill_task_context(node: Tag) -> bool:
    """Er noden i en oppgave-/utfyllingskontekst?"""
    p = node
    while p is not None:
        if isinstance(p, Tag):
            n = (p.name or "").lower()
            if n in _SKIP_CONTAINERS:
                return False
            if n in {"section", "article", "div", "li", "p", "span"}:
                cls = set(p.get("class", []) or [])
                if "task" in cls:
                    return True
                if _epub_types(p) & _TASK_TOKENS:
                    return True
        p = getattr(p, "parent", None)
    return False

def _normalize_word_blank(text: str) -> str:
    """
    Normaliser 'ord-blank' til fire punktum '....':
    - '…' (enkelt eller flere) → '....'
    - '...' / '......' / '. . .' etc. → '....'
    NB: Ikke rør underscores – de skal representere antall manglende bokstaver.
    """
    # erstatt alle 'box' tegn med '....'
    s = BOX_RX.sub("....", text)
    # normaliser ellipsis / dot-run til '....'
    # erstatt alle forekomster av 3+ dot/ellipsis til fire punktum
    s = ELLIPSIS_RX.sub("....", s)
    return s

def _is_only_four_dots(text: str) -> bool:
    """True hvis teksten (trimmet for whitespace og hermetegn) er bare fire punktum."""
    t = text.strip()
    # Hvis innhold er i hermetegn '....' eller "....", regn det som bare fire punktum også.
    if t in {"....", "'....'", '"...."'}:
        return True
    return False

def _replace_p_four_dots_with_inline(p: Tag):
    """
    Erstatt <p> som kun inneholder '....' (ev. i hermetegn) med inline
    <span class="asciimath">'....'</span> (for å unngå paragraf med bare blank).
    """
    span = p.new_tag("span")
    span["class"] = ["asciimath"]
    # bruk enslige hermetegn rundt innhold slik eksemplet viser
    span.string = "'....'"
    p.replace_with(span)

# --- Hjelpere for §2.5.1.8 ------------------------------------------------------

def _in_fill_blank_container(el: Tag) -> bool:
    """Er vi i relevant oppgavekontekst?"""
    p = el
    while p is not None:
        if isinstance(p, Tag):
            if _epub_types(p) & _TASK_TOKENS:
                return True
            cls = set(p.get("class", []) or [])
            if "task" in cls:
                return True
        p = p.parent
    return False

def _collect_given_words(answer_el: Tag) -> list[str]:
    """Hent ord fra <* epub:type='answer'>.
    - Støtter tekst, <li>, <span> m.m.
    - Fjerner paranteser rundt ord, trimmer og filtrerer tomme.
    """
    parts = []

    # 1) <li>-elementer
    for li in answer_el.find_all("li"):
        t = li.get_text(" ", strip=True)
        if t:
            parts.append(t)

    # 2) Ellers – fri tekst i answer_el
    if not parts:
        raw = answer_el.get_text(" ", strip=True)
        if raw:
            # fjern ytre parenteser hvis hele svaret er i ()
            m = _PARENS_BLOCK_RX.match(raw)
            if m and m.group(1):
                raw = m.group(1)
            # splitt på ; , / eller “dobbel/mye whitespace”
            parts = [p.strip() for p in _WORD_SPLIT_RX.split(raw) if p.strip()]
            if not parts:
                parts = [raw.strip()]

    # normaliser – fjern eventuelle ytre hermetegn/paranteser per ord
    norm = []
    for w in parts:
        w = w.strip().strip("()[]{}\"'“”‘’").strip()
        if w:
            norm.append(w)
    return norm

def _find_question_blocks(container: Tag) -> list[Tag]:
    """Finn element(er) med epub:type='question' under en problemkonteiner.
    Hvis ingen, bruk containeren selv."""
    qs = container.find_all(attrs={"epub:type": True})
    blocks = [q for q in qs if "question" in _epub_types(q)]
    return blocks or [container]

def _find_blank_hosts(q: Tag) -> list[Tag]:
    """Finn steder (p eller li) i spørsmålet som inneholder en blank."""
    hosts = []
    # Vi foretrekker <p> og <li> (setningsblokker)
    for el in q.find_all(["p", "li"]):
        if _BLANK_SENTENCE_RX.search(el.get_text("", strip=True) or ""):
            hosts.append(el)
    # Hvis ingen p/li, og spørsmålet er ren tekst – bruk q selv
    if not hosts and _BLANK_SENTENCE_RX.search(q.get_text("", strip=True) or ""):
        hosts = [q]
    return hosts

def _already_has_trailing_parens(host: Tag, words_joined: str) -> bool:
    """Idempotens: sjekk om host slutter med ('ord, ord')."""
    txt = host.get_text("", strip=True)
    return txt.endswith(f"({words_joined})")

def _append_parens_after(host: Tag, words: list[str]) -> bool:
    """Legg til ' (a, b, c)' på slutten av host – intakt markup, skånsom spacing."""
    if not words:
        return False
    joined = ", ".join(words)
    if _already_has_trailing_parens(host, joined):
        return False

    # legg inn som ren tekstnode på slutten
    # sørg for at siste node finnes
    if not host.contents:
        host.append(NavigableString(f" ({joined})"))
        return True

    last = host.contents[-1]
    # hvis siste er NavigableString → bare append
    if isinstance(last, NavigableString):
        # pass på mellomrom
        s = str(last)
        if s.endswith(" "):
            last.replace_with(s + f"({joined})")
        else:
            last.replace_with(s + f" ({joined})")
    else:
        host.append(NavigableString(f" ({joined})"))
    return True

def _neutralize_answer(answer_el: Tag):
    """Skjul/fjern answer-elementet etter at vi har flyttet ordene.
    Idempotent: vi merker det i data-attributt i stedet for å slette hardt hvis ønskelig.
    """
    # Hvis du vil fjerne helt:
    answer_el.decompose()
    # Alternativ:
    # answer_el["data-moved-to-question"] = "true"
    # answer_el.decompose()

# --- Hjelpere for §2.5.1.9 ------------------------------------------------------

def _in_task_context(el: Tag) -> bool:
    p = el
    while p is not None:
        if isinstance(p, Tag) and (p.name in {"section","article","div","li","p","span"}):
            if "task" in (p.get("class") or []): return True
            if _epub_types(p) & _TASK_TOKENS:    return True
        p = getattr(p, "parent", None)
    return False

def _in_fill_blank_context(el: Tag) -> bool:
    p = el
    while p is not None:
        if isinstance(p, Tag):
            if _epub_types(p) & _FILL_TOKENS:
                return True
        p = getattr(p, "parent", None)
    return False

def _is_line_only_text(s: str) -> bool:
    """Hele teksten er bare 'linje' (ikke akkurat fire punktum)."""
    t = (s or "").strip()
    if t in {"....", "'....'", '"...."'}:
        return False
    return bool(TRAILING_LINE_RX.fullmatch(t))

def _strip_trailing_lines_in_block(block: Tag) -> bool:
    """Fjern trailing 'linje'-mønster i en <p>/<li> uten å røre innhold før det."""
    txt = block.get_text("", strip=False)
    new = TRAILING_LINE_RX.sub("", txt)
    if new != txt:
        # Skånsom erstatning: sett hele blokka til kun 'new' (ren tekst)
        # Hvis du vil bevare inline-markup før linjene, må du gjøre mer granular parsing.
        for c in list(block.contents):
            c.extract()
        block.append(NavigableString(new.rstrip()))
        return True
    return False

def _is_liney_element(tag: Tag) -> bool:
    """Er dette en node som representerer 'linje' og kan fjernes?"""
    if tag.name == "hr":
        return True
    if tag.name in {"input", "textarea"}:
        return True
    # border-bottom i inline-style
    style = (tag.get("style") or "").lower()
    if "border-bottom" in style:
        return True
    # klassehint
    cls = {c.lower() for c in (tag.get("class") or [])}
    if {"line", "answer-line", "dotted-line"} & cls:
        return True
    # ren tekst i f.eks. <span>/<p> som bare er linjer
    if tag.name in {"span", "p", "div"}:
        if _is_line_only_text(tag.get_text("", strip=True)):
            return True
    return False

def _convert_2col_table_to_question_list(tbl: Tag, soup, logger) -> bool:
    """
    To-kolonne tabell der kolonne 2 er 'linje' → konverter til <ol> med spørsmål (kolonne 1).
    """
    rows = tbl.find_all("tr")
    if not rows:
        return False
    body_rows = [r for r in rows if r.find_parent("tbody") or (not r.find_parent("thead") and not r.find_parent("tfoot"))]
    if not body_rows:
        body_rows = rows
    # Sjekk at alle rader har 2 celler
    for r in body_rows:
        cells = r.find_all(["td","th"], recursive=False)
        if len(cells) != 2:
            return False
    # Sjekk at høyre kolonne *ser ut som* linjer i flertallet av rader
    right_is_line = 0
    for r in body_rows:
        right = r.find_all(["td","th"], recursive=False)[1]
        if _is_line_only_text(right.get_text(" ", strip=True)) or right.find(["hr","input","textarea"]):
            right_is_line += 1
    if right_is_line < max(1, len(body_rows)//2):
        return False  # for usikkert

    # Lag <ol> og fyll med venstre celle-innhold
    ol = soup.new_tag("ol")
    for r in body_rows:
        left = r.find_all(["td","th"], recursive=False)[0]
        li = soup.new_tag("li")
        # flytt *innhold* av venstre celle inn i li
        for n in list(left.contents):
            li.append(n.extract())
        ol.append(li)

    tbl.insert_before(ol)
    tbl.decompose()
    logger.debug("2.5.1.9 - Converted 2-col table to questions list")
    return True

# --- Hjelpere for §2.5.1.10 ------------------------------------------------------

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _label_across(lang: str) -> str:
    return "Across" if lang.startswith("en") else "Vannrett"

def _label_down(lang: str) -> str:
    return "Down" if lang.startswith("en") else "Loddrett"

def _normalize_ul_plain(lst: Tag) -> bool:
    if lst.name != "ul":
        return False
    changed = False
    cls = set(lst.get("class", []) or [])
    style = (lst.get("style") or "").strip().lower()
    # alt som tyder på kuleløs liste → class=list-unstyled
    if ("plain" in cls) or ("list-style-type-none" in cls) or ("list-unstyled" in cls) or ("list-style-type:none" in style) or ("list-style: none" in style):
        if "list-unstyled" not in cls:
            cls.add("list-unstyled"); lst["class"] = list(cls); changed = True
        if "style" in lst.attrs:
            new_style = re.sub(r"(?:^|;)\s*list-style-type\s*:\s*none\s*;?", "", lst["style"], flags=re.I).strip()
            if new_style: lst["style"] = new_style
            else: del lst["style"]
            changed = True
    return changed

def _ensure_list_title_before(lst: Tag, title_text: str) -> bool:
    prev = lst.previous_sibling
    while isinstance(prev, NavigableString) and not prev.strip():
        prev = prev.previous_sibling
    if isinstance(prev, Tag) and prev.name == "p" and prev.get_text("", strip=True) == title_text:
        return False
    p = lst.new_tag("p"); p.string = title_text
    lst.insert_before(p)
    return True

def _guess_list_role(lst: Tag, lang: str) -> str | None:
    """Forsøk å lese 'Across/Vannrett' vs 'Down/Loddrett' fra nærliggende heading/p."""
    # Sjekk forrige element
    prev = lst.previous_sibling
    while isinstance(prev, NavigableString) and not prev.strip():
        prev = prev.previous_sibling
    if isinstance(prev, Tag):
        txt = prev.get_text(" ", strip=True).lower()
        if "across" in txt or "vannrett" in txt:
            return "across"
        if "down" in txt or "loddrett" in txt:
            return "down"
    # Sjekk nærmeste heading over
    cur = lst.previous_sibling
    while isinstance(cur, Tag):
        name = getattr(cur, "name", "") or ""
        if _HEADING_RX.match(name):
            t = cur.get_text(" ", strip=True).lower()
            if "across" in t or "vannrett" in t:
                return "across"
            if "down" in t or "loddrett" in t:
                return "down"
            break
        cur = cur.previous_sibling
    return None

def _ensure_ul_not_ol(lst: Tag) -> Tag:
    if lst.name == "ul":
        return lst
    # konverter <ol> → <ul>
    ul = lst.new_tag("ul")
    # behold items
    for c in list(lst.contents):
        ul.append(c.extract())
    lst.replace_with(ul)
    return ul

def _has_crossword_image(container: Tag) -> bool:
    # enten direkte <img>, eller <figure><img>
    if container.find("img"):
        return True
    if container.find("figure") and container.find("figure").find("img"):
        return True
    return False

# --- Hjelpere for §2.5.1.11 ------------------------------------------------------

def _get_text(node) -> str:
    return "" if node is None else (node.get_text("", strip=True) if isinstance(node, Tag) else str(node).strip())

def _single_unicode_letter(s: str) -> str | None:
    # Normaliser til NFC for å få prekomponerte tegn der det er mulig
    t = unicodedata.normalize("NFC", (s or "").strip())
    # Én enkelt bokstav?
    if len(t) == 1 and t.isalpha():
        return t.lower()
    return None

def _is_letter_cell(td: Tag) -> bool:
    return _single_unicode_letter(_get_text(td)) is not None

def _cell_letter(td: Tag) -> str | None:
    return _single_unicode_letter(_get_text(td))

def _table_is_wordsearch(tbl: Tag) -> tuple[bool, list[list[str]]]:
    """
    Returnerer (is_wordsearch, rows_letters)
    rows_letters = liste av rader, hver rad en liste med bokstaver (små).
    Tabell må være minst 3x3 og alle celler én bokstav.
    """
    rows = [tr for tr in tbl.find_all("tr", recursive=False)]
    if len(rows) < 3:
        return False, []
    grid: list[list[str]] = []
    cols_count = None
    for tr in rows:
        cells = tr.find_all(["td", "th"], recursive=False)
        if len(cells) < 3:
            return False, []
        row_letters = []
        for c in cells:
            if not _is_letter_cell(c):
                return False, []
            ch = _cell_letter(c)
            if ch is None:
                return False, []
            row_letters.append(ch)
        if cols_count is None:
            cols_count = len(row_letters)
        elif len(row_letters) != cols_count:
            return False, []  # ujevn bredde
        grid.append(row_letters)
    return True, grid

def _ensure_figcaption_copied(tbl: Tag, fig: Tag):
    # Hvis det finnes en <caption> under tabellen, konverter til <figcaption>
    cap = tbl.find("caption")
    if cap:
        figcap = fig.new_tag("figcaption")
        # flytt innhold
        for n in list(cap.contents):
            figcap.append(n.extract())
        fig.append(figcap)

# --- Hjelpere for 2.5.1.12 ----------------------------------------------------

def _is_task_container(el):
    if not getattr(el, "name", None):
        return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls:
        return True
    if _epub_types(el) & TASKISH_TOKENS:
        return True
    return False

def _in_task_or_key_ancestor(node):
    p = node
    while p is not None:
        if _is_task_container(p):
            return True
        p = getattr(p, "parent", None)
    return False

# --- Hjelpere for 2.5.1.13 ----------------------------------------------------

def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls: return True
    return bool(_epub_types(el) & TASKISH_TOKENS)

def _in_task_ancestor(node: Tag) -> bool:
    p = node
    while p is not None:
        if _is_task_container(p): return True
        p = getattr(p, "parent", None)
    return False

def _text(node) -> str:
    if node is None: return ""
    if isinstance(node, NavigableString): return str(node)
    return node.get_text(" ", strip=True) or ""

def _parse_css_px(style: str, prop: str) -> float | None:
    if not style: return None
    m = re.search(rf"{prop}\s*:\s*(-?\d+(?:\.\d+)?)px", style, flags=re.I)
    return float(m.group(1)) if m else None

def _has_generated_board_list(container: Tag) -> Tag | None:
    # Finn en eksisterende generert liste rett etter containeren
    sib = container.next_sibling
    while isinstance(sib, NavigableString) and not sib.strip():
        sib = sib.next_sibling
    if isinstance(sib, Tag) and sib.name in {"ol","ul"}:
        classes = set(sib.get("class", []) or [])
        if "boardgame-list" in classes:
            return sib
    return None

def _mk_list(soup, ordered: bool):
    if ordered:
        lst = soup.new_tag("ol")
    else:
        lst = soup.new_tag("ul")
        # unstyled for å unngå ekstra bullets om ønskelig
        cls = set(lst.get("class", []) or [])
        cls.add("list-unstyled")
        lst["class"] = list(cls)
    # felles klasse for idempotens
    cls = set(lst.get("class", []) or [])
    cls.add("boardgame-list")
    lst["class"] = list(cls)
    return lst

# --- trekk ut bokser fra ulike kildetyper ------------------------------------

def _extract_table_boxes(table: Tag):
    """Returner (ok, boxes, meta): boxes = [{'text', 'row', 'col'}]."""
    rows = table.find_all("tr", recursive=False)
    if len(rows) < 2: return False, [], {}
    boxes = []
    for r_idx, tr in enumerate(rows):
        cells = tr.find_all(["td","th"], recursive=False)
        if not cells: continue
        for c_idx, td in enumerate(cells):
            txt = _text(td)
            if not txt: continue
            # hopp over tydelig dekor (enkelt bindestrek etc.)
            if txt.strip() in {"-", "—", "–"}: continue
            boxes.append({"text": txt, "row": r_idx, "col": c_idx})
    return (len(boxes) >= 6), boxes, {"kind": "table"}

def _extract_abspos_boxes(container: Tag):
    """Se etter elementer med position:absolute; top/left og tekst."""
    boxes = []
    for el in container.find_all(True):
        if not getattr(el, "name", None): continue
        style = (el.get("style") or "").lower()
        if "position:absolute" not in style: continue
        top  = _parse_css_px(style, "top")
        left = _parse_css_px(style, "left")
        if top is None or left is None: continue
        txt = _text(el)
        if not txt: continue
        # filtrer bort veldig korte symboler som ofte er pynt (men behold tall/bokstaver)
        if len(txt.strip()) == 1 and not txt.strip().isalnum():
            continue
        boxes.append({"text": txt, "top": top, "left": left})
    return (len(boxes) >= 6), boxes, {"kind": "abspos"}

def _extract_class_boxes(container: Tag):
    """Se etter 'box/tile/square/space'-klasser."""
    boxes = []
    for el in container.find_all(True):
        cls = set(el.get("class", []) or [])
        if not (cls & BOX_CLASS_HINTS): continue
        txt = _text(el)
        if not txt: continue
        boxes.append({"text": txt})
    return (len(boxes) >= 6), boxes, {"kind": "class"}

# --- sortering / ordensregler -------------------------------------------------

def _ordered_by_leading_number(items: list[dict]) -> tuple[bool, list[tuple[int,str]]]:
    out = []
    for it in items:
        m = _NUM_PREFIX_RX.match(it["text"])
        if not m: return False, []
        num = int(m.group(1))
        rest = m.group(2).strip()
        out.append((num, rest if rest else it["text"]))
    out.sort(key=lambda x: x[0])
    return True, out

def _by_abspos(items: list[dict]) -> list[str]:
    items = sorted(items, key=lambda x: (x.get("top", 0.0), x.get("left", 0.0)))
    return [it["text"] for it in items]

def _by_table_rc(items: list[dict]) -> list[str]:
    items = sorted(items, key=lambda x: (x.get("row", 0), x.get("col", 0)))
    return [it["text"] for it in items]

# --- Hjelpere for 2.5.1.14 ----------------------------------------------------
def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None):
        return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls:
        return True
    return bool(_epub_types(el) & _TASKISH_TOKENS)

def _is_inline_only_p(p: Tag) -> bool:
    # p skal kun inneholde inline; tillat <span>/<a>/<em>/<strong>/<img>/<br>/<code> osv.
    for d in p.descendants:
        if isinstance(d, Tag) and d.name in _BLOCK_TAGS and d is not p:
            return False
    return True

def _is_bridgehead(p: Tag) -> bool:
    et = (p.get("epub:type") or "").lower()
    if "bridgehead" in et:
        return True
    # noen ganger brukes <p class="bridgehead">
    cls = " ".join(p.get("class", [])).lower()
    return "bridgehead" in cls

def _looks_like_list_p(p: Tag) -> bool:
    # p med rent inline-innhold regnes som kandidat
    if not _is_inline_only_p(p):
        return False
    # ikke headings/bridgeheads
    if _is_bridgehead(p):
        return False
    # ikke allerede inni <li>
    anc = p.parent
    while anc is not None:
        if getattr(anc, "name", "") in {"li","ul","ol"}:
            return False
        anc = anc.parent
    # ellers OK
    return True

def _normalize_unstyled_ul(ul: Tag) -> bool:
    """Sett class=list-unstyled for kuleløse UL-er; fjern list-style-type:none; idempotent."""
    changed = False
    style = (ul.get("style") or "").lower().replace(" ", "")
    cls = set(ul.get("class", []) or [])
    # sterke indikatorer på kuleløs liste
    if "list-unstyled" in cls or "plain" in cls or "list-style-type-none" in cls or "list-style-type:none;" in style:
        if "list-unstyled" not in cls:
            cls.add("list-unstyled"); ul["class"] = list(cls); changed = True
        # fjern eksplisitt style hvis den kun var for bullets
        if "style" in ul.attrs and "list-style-type" in ul["style"].lower():
            new_style = re.sub(r"(?:^|;)\s*list-style-type\s*:\s*none\s*;?", "", ul["style"], flags=re.I).strip()
            if new_style:
                ul["style"] = new_style
            else:
                del ul["style"]
            changed = True
    return changed

def _mk_ul_unstyled(soup):
    ul = soup.new_tag("ul")
    ul["class"] = ["list-unstyled", "generated-unstyled"]
    return ul

# --- Hjelpere for 2.5.1.15 ----------------------------------------------------
def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None):
        return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls:
        return True
    return bool(_epub_types(el) & _TASKISH_TOKENS)

def _leading_token_kind(text: str) -> str:
    """Returner 'std', 'roman', 'nonstd' eller 'none' basert på ledetekst."""
    s = (text or "")
    if _STD_INT_TOKEN_RX.match(s):
        return "std"
    if _STD_ROMAN_TOKEN_RX.match(s):
        return "roman"  # betrakter vi som 'std' i denne sammenheng
    if _NONSTD_TOKEN_RX.match(s):
        return "nonstd"
    return "none"

def _to_ol(element: Tag, soup) -> Tag:
    """Konverter <ul>→<ol> idempotent. Returner <ol>."""
    if element.name == "ol":
        return element
    ol = soup.new_tag("ol")
    # flytt klasser/attrs med unntak av 'type' (irrelevant) – men vi overskriver klassene senere
    for k, v in list(element.attrs.items()):
        if k not in {"type"}:
            ol.attrs[k] = v
    for c in list(element.contents):
        ol.append(c.extract())
    element.replace_with(ol)
    return ol

def _mark_list_type_none(ol: Tag):
    """Sett class='list-type-none' og style for list-style-type:none; idempotent."""
    # klasser
    classes = set(ol.get("class", []) or [])
    if "list-type-none" not in classes:
        classes.add("list-type-none")
        ol["class"] = list(classes)
    # style
    style = (ol.get("style") or "")
    if "list-style-type" not in style.lower():
        if style and not style.strip().endswith(";"):
            style += ";"
        style += " list-style-type: none;"
        ol["style"] = style.strip()
    # fjern ol-type/start; li-value
    for attr in ("type", "start"):
        if attr in ol.attrs:
            del ol.attrs[attr]
    for li in ol.find_all("li", recursive=False):
        if "value" in li.attrs:
            del li.attrs["value"]

# --- Hjelpere for 2.5.1.16 ----------------------------------------------------

# --- konfig/heuristikk --------------------------------------------------------

def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "task" in cls: return True
    et = _epub_types(el)
    return bool(et & _TASKISH_TOKENS)

def _is_answer_section(el: Tag) -> bool:
    # Unngå å røre fasit/svar-seksjoner
    cls = set(el.get("class", []) or [])
    if "key" in cls: return True
    et = _epub_types(el)
    return bool(et & _ANSWERISH_TOKENS)

def _text(n) -> str:
    if n is None: return ""
    if isinstance(n, NavigableString): return str(n)
    return n.get_text(" ", strip=True) or ""

def _is_inline_only(tag: Tag) -> bool:
    for d in tag.descendants:
        if isinstance(d, Tag) and d.name in _BLOCK_TAGS and d is not tag:
            return False
    return True

def _looks_like_example_node(node: Tag) -> bool:
    # epub:type-hint
    et = _epub_types(node)
    if et & (_ANSWERISH_TOKENS | _EXAMPLEISH_TOKENS):
        return True
    # class-hint
    cls = " ".join(node.get("class", [])).lower()
    if any(tok in cls for tok in ("answer","fasit","eksempel","example","sample","model")):
        return True
    # tekst-prefiks
    txt = _text(node)
    if _EXAMPLE_PREFIX_RX.match(txt):
        return True
    return False

def _clean_example_text(txt: str) -> str:
    # Fjern språk-prefiks ("Svar:", "Example answer:" osv.)
    cleaned = _EXAMPLE_PREFIX_RX.sub("", txt or "").strip()
    # komprimer whitespace
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    # fjern avsluttende punktum om det seiler rett før parentesen (smakssak)
    return cleaned

def _li_has_same_parenthetical(li: Tag, example_text: str) -> bool:
    if not example_text:
        return False
    # Ganske enkel sjekk: finnes "(example_text)" allerede i li-tekst?
    li_txt = li.get_text(" ", strip=True)
    return f"({example_text})" in li_txt

def _insertion_anchor_inside_li(li: Tag):
    # Sett inn før første nested liste hvis den finnes, ellers på slutten
    for child in li.find_all(recursive=False):
        if getattr(child, "name", "") in {"ol","ul"}:
            return child
    return None

# --- Hjelpere for 2.5.1.17 ----------------------------------------------------
def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls: return True
    return bool(_epub_types(el) & _TASKISH_TOKENS)

def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html: return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _text(n) -> str:
    if n is None: return ""
    if isinstance(n, NavigableString): return str(n)
    return n.get_text(" ", strip=True) or ""

def _rows(tbl: Tag): return tbl.find_all("tr", recursive=False)
def _cells(tr: Tag): return tr.find_all(["td","th"], recursive=False)

def _is_checkboxy_cell(cell: Tag) -> bool:
    if cell.find(lambda t: getattr(t, "name", "") == "input" and (t.get("type") or "").lower() == "checkbox"):
        return True
    if cell.find("svg"): return True
    txt = _text(cell)
    if txt and (txt.strip() in {"x","X"} or any(ch in _CHECK_GLYPHS for ch in txt)): return True
    img = cell.find("img")
    if img:
        alt = (img.get("alt") or "").lower()
        if any(k in alt for k in ("check","checkbox","tick","kryss","avkryss")):
            return True
    return False

def _detect_ticking_table(table: Tag):
    rows = _rows(table)
    if len(rows) < 2: return False, [], [], None

    header = rows[0] if rows and any(c.name=="th" for c in _cells(rows[0])) else None
    body_rows = rows[1:] if header else rows

    if not body_rows: return False, [], [], None
    num_cols = max(len(_cells(r)) for r in body_rows) or 0
    if num_cols < 2: return False, [], [], None

    row_count = 0
    checkbox_counts = [0]*num_cols
    for r in body_rows:
        cs = _cells(r)
        if not cs: continue
        row_count += 1
        for j, c in enumerate(cs):
            txt = _text(c)
            if _is_checkboxy_cell(c) or not txt.strip():
                checkbox_counts[j] += 1

    checkbox_cols = {j for j in range(1, num_cols) if row_count and (checkbox_counts[j]/row_count) >= 0.8}
    if not checkbox_cols: return False, [], [], None

    headings = []
    if header:
        for j, c in enumerate(_cells(header)):
            if j == 0: continue
            if j in checkbox_cols:
                h = _text(c).strip()
                if h: headings.append(h)

    # påstander = første kolonne
    statements = []
    for r in body_rows:
        cs = _cells(r)
        if not cs: continue
        s = _text(cs[0]).strip()
        if s: statements.append(s)

    return True, headings, statements, header

def _normalize_headings(headings: list[str], lang: str) -> str:
    # normaliser til Ja/Nei, Riktig/Feil, True/False, Yes/No
    lower = [h.lower() for h in headings]
    if {"ja","nei"} <= set(lower): return "Ja/Nei"
    if {"riktig","feil"} <= set(lower): return "Riktig/Feil"
    if {"true","false"} <= set(lower): return "True/False"
    if {"yes","no"} <= set(lower): return "Yes/No"
    # fallback pr språk
    if lang.startswith("en"): return "True/False"
    return "Ja/Nei"

def _make_head_p(soup, text: str):
    p = soup.new_tag("p")
    p["class"] = ["ticking-boxes-head"]
    p.string = text
    return p

def _existing_head_p(node_after: Tag) -> Tag | None:
    # Finn nærmeste forrige <p.ticking-boxes-head>
    prev = node_after.previous_sibling
    while isinstance(prev, NavigableString) and not prev.strip():
        prev = prev.previous_sibling
    if isinstance(prev, Tag) and prev.name == "p" and "ticking-boxes-head" in (prev.get("class", []) or []):
        return prev
    return None

def _existing_ticking_list(node_after: Tag) -> Tag | None:
    nxt = node_after.next_sibling
    while isinstance(nxt, NavigableString) and not nxt.strip():
        nxt = nxt.next_sibling
    if isinstance(nxt, Tag) and nxt.name in {"ol","ul"} and "ticking-boxes-list" in (nxt.get("class", []) or []):
        return nxt
    return None

def _make_list_from_statements(soup, statements: list[str], ordered=True):
    lst = soup.new_tag("ol" if ordered else "ul")
    classes = set(lst.get("class", []) or [])
    classes.add("ticking-boxes-list")
    if not ordered:
        classes.add("list-unstyled")
    lst["class"] = list(classes)
    for s in statements:
        li = soup.new_tag("li")
        li.append(NavigableString(re.sub(r"\s+", " ", s).strip()))
        lst.append(li)
    return lst

def _strip_leading_number(text: str) -> str:
    return _LEADING_NUM_RX.sub("", text or "").strip()

def _convert_numbered_p_run_to_list(p_run: list[Tag], soup) -> Tag:
    """Konverter ≥2 nummererte <p> til <ol class='ticking-boxes-list'> og returner lista."""
    ol = soup.new_tag("ol")
    ol["class"] = ["ticking-boxes-list"]
    for p in p_run:
        li = soup.new_tag("li")
        li.append(NavigableString(_strip_leading_number(_text(p))))
        ol.append(li)
    # Sett inn ol før første p, fjern p-ene
    first = p_run[0]
    first.insert_before(ol)
    for p in p_run:
        p.decompose()
    return ol

def _find_numbered_p_run(anchor: Tag) -> list[Tag]:
    """
    Finn en sekvens av nummererte <p> rett før/etter 'anchor' (tabellen).
    Krever minst 2 for å være trygg.
    """
    # Sjekk før anchor
    run = []
    prev = anchor.previous_sibling
    while isinstance(prev, NavigableString) and not prev.strip():
        prev = prev.previous_sibling
    cur = prev
    while isinstance(cur, Tag) and cur.name == "p" and _LEADING_NUM_RX.match(_text(cur)):
        run.insert(0, cur)  # bygg i riktig rekkefølge
        cur = cur.previous_sibling
        while isinstance(cur, NavigableString) and not cur.strip():
            cur = cur.previous_sibling
    if len(run) >= 2:
        return run
    # Sjekk etter anchor
    run = []
    nxt = anchor.next_sibling
    while isinstance(nxt, NavigableString) and not nxt.strip():
        nxt = nxt.next_sibling
    cur = nxt
    while isinstance(cur, Tag) and cur.name == "p" and _LEADING_NUM_RX.match(_text(cur)):
        run.append(cur)
        cur = cur.next_sibling
        while isinstance(cur, NavigableString) and not cur.strip():
            cur = cur.next_sibling
    if len(run) >= 2:
        return run
    return []

# --- Hjelpere for 2.5.1.18 ----------------------------------------------------
def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls: return True
    return bool(_epub_types(el) & _TASKISH_TOKENS)

def _text(n) -> str:
    if n is None: return ""
    if isinstance(n, NavigableString): return str(n)
    return n.get_text(" ", strip=True) or ""

def _rows(tbl: Tag): return tbl.find_all("tr", recursive=False)
def _cells(tr: Tag): return tr.find_all(["td","th"], recursive=False)

def _is_inline_only(tag: Tag) -> bool:
    for d in tag.descendants:
        if isinstance(d, Tag) and d.name in _BLOCK_TAGS and d is not tag:
            return False
    return True

def _is_simple_layout_table(tbl: Tag, *, aggressive=False) -> tuple[bool, list[str], list[list[str]]]:
    """
    Returnerer (ok, headers, rows) for tabeller som egner seg å konvertere til liste.
    - 2–4 kolonner, minst 2 rader.
    - celler med primært inline-innhold, ikke “tunge” blokker.
    - 'aggressive': senker terskler (tillater litt lengre celler osv.).
    """
    trs = _rows(tbl)
    if len(trs) < 2:
        return False, [], []

    # finn antall kolonner
    ncols = max((len(_cells(tr)) for tr in trs), default=0)
    if ncols < 2 or ncols > 4:
        return False, [], []

    # skiln header/body
    header = None
    if any(c.name == "th" for c in _cells(trs[0])):
        header = trs[0]
        body = trs[1:]
    else:
        body = trs

    # tom/for kort body?
    if len(body) < 1:
        return False, [], []

    headers = []
    if header:
        for c in _cells(header):
            headers.append(_text(c).strip())

    # valider innholdsceller
    rows = []
    max_cell_len = 160 if not aggressive else 280
    for tr in body:
        cs = _cells(tr)
        if not cs: 
            continue
        row = []
        for c in cs:
            if not _is_inline_only(c):
                return False, [], []  # inneholder blokkelementer → sannsynlig data-tabell
            t = re.sub(r"\s+", " ", _text(c)).strip()
            if len(t) > max_cell_len and not aggressive:
                return False, [], []  # veldig lange celler → sannsynlig data-tabell
            row.append(t)
        # minst én celle bør ha tekst
        if any(s for s in row):
            rows.append(row)

    if len(rows) < 2 and not aggressive:
        return False, [], []

    return True, headers, rows

def _existing_table_as_list(node_after: Tag) -> Tag | None:
    nxt = node_after.next_sibling
    while isinstance(nxt, NavigableString) and not nxt.strip():
        nxt = nxt.next_sibling
    if isinstance(nxt, Tag) and nxt.name in {"ol","ul"}:
        classes = set(nxt.get("class", []) or [])
        if "table-as-list" in classes:
            return nxt
    return None

def _make_head_p(soup, headers: list[str]) -> Tag:
    p = soup.new_tag("p")
    p["class"] = ["table-as-list-head"]
    # spesifikasjonen: bruk semikolon + blank
    p.string = "; ".join(h for h in headers if h.strip())
    return p

def _make_ul_from_rows(soup, rows: list[list[str]]) -> Tag:
    ul = soup.new_tag("ul")
    ul["class"] = ["list-unstyled", "table-as-list"]
    for row in rows:
        # spesifikasjonen: separer kolonner med '; '
        content = "; ".join([s for s in row if s])
        if not content:
            continue
        li = soup.new_tag("li")
        li.append(NavigableString(content))
        ul.append(li)
    return ul

# --- Hjelpere for 2.5.1.19 ----------------------------------------------------
def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "task" in cls or "key" in cls: return True
    return bool(_epub_types(el) & _TASKISH_TOKENS)

def _text(n) -> str:
    if n is None: return ""
    if isinstance(n, NavigableString): return str(n)
    return n.get_text(" ", strip=True) or ""

def _is_inline_only(tag: Tag) -> bool:
    for d in tag.descendants:
        if isinstance(d, Tag) and d.name in _BLOCK_TAGS and d is not tag:
            return False
    return True

def _first_sig_child(tag: Tag):
    for c in tag.contents:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        return c
    return None

def _collect_between_siblings(parent: Tag, left: Tag, right: Tag):
    """
    Samle *alle* noder som ligger mellom left<li> og right<li> som er egnet som 'mellomtekst'.
    Tillater <p> (inline-only), <br>, og rent inline (span/em/strong/i/b/a/img osv.)/tekst.
    """
    out = []
    cur = left.next_sibling
    allowed_inline = {"span","em","strong","i","b","u","a","img","sup","sub","code","kbd","s","small","mark"}
    while cur is not None and cur is not right:
        nxt = cur.next_sibling
        if isinstance(cur, NavigableString):
            if cur.strip():
                out.append(cur)
            else:
                # ignorer ren whitespace
                pass
        elif isinstance(cur, Tag):
            nm = cur.name
            if nm == "p" and _is_inline_only(cur):
                out.append(cur)
            elif nm == "br":
                out.append(cur)
            elif nm in allowed_inline:
                out.append(cur)
            else:
                # blokker/lister/figure osv. lar vi stå (ikke mellomtekst)
                pass
        cur = nxt
    return out

def _wrap_into_paragraphs(soup, nodes: list):
    """
    Lag en liste av <p> fra 'nodes'.
    - Eksisterende <p> beholdes som egne avsnitt (flyttes).
    - Inline/tekst grupperes til <p>, og <br> avslutter gjeldende avsnitt.
    """
    paras = []
    buffer_inline = []

    def flush_buffer():
        nonlocal buffer_inline, paras
        if buffer_inline:
            p = soup.new_tag("p")
            for n in buffer_inline:
                p.append(n)
            paras.append(p)
            buffer_inline = []

    for n in nodes:
        if isinstance(n, Tag) and n.name == "p":
            flush_buffer()
            paras.append(n)  # flytt hele <p> som den er
        elif isinstance(n, Tag) and n.name == "br":
            flush_buffer()
            # <br> blir ikke beholdt; den fungerer bare som avsnittsskille
            try:
                n.decompose()
            except Exception:
                pass
        else:
            # inline/tekst
            # sørg for at n er frakoblet før vi legger i buffer
            try:
                n.extract()
            except Exception:
                pass
            buffer_inline.append(n if isinstance(n, Tag) else NavigableString(str(n)))

    flush_buffer()
    # fjern tomme <p>
    paras = [p for p in paras if p.get_text("", strip=True)]
    return paras

# --- Hjelpere for 2.5.2 ----------------------------------------------------

def _is_task_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "task" in cls: return True
    return bool(_epub_types(el) & _TASKISH_TOKENS)

def _is_answer_container(el: Tag) -> bool:
    if not getattr(el, "name", None): return False
    cls = set(el.get("class", []) or [])
    if "key" in cls: return True
    return bool(_epub_types(el) & _ANSWERISH_TOKENS)

def _nearest_heading_level(node: Tag) -> int:
    # finn nærmeste heading over, og bruk +1 (maks h6)
    anc = node
    while anc is not None:
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 3

def _roman(n: int, upper=True) -> str:
    vals = [(1000,'M'),(900,'CM'),(500,'D'),(400,'CD'),(100,'C'),(90,'XC'),(50,'L'),(40,'XL'),(10,'X'),(9,'IX'),(5,'V'),(4,'IV'),(1,'I')]
    out = []
    x = max(1, min(n, 3999))
    for v, s in vals:
        while x >= v:
            out.append(s)
            x -= v
    s = "".join(out)
    return s if upper else s.lower()

def _alpha(n: int, upper=False) -> str:
    # 1->a, 27->aa (som CSS counters)
    n = max(1, n)
    chars = []
    while n > 0:
        n -= 1
        chars.append(chr((n % 26) + ord('A' if upper else 'a')))
        n //= 26
    return "".join(reversed(chars))

def _ol_token_for_index(ol: Tag, idx0_based: int, li_value: int | None) -> str:
    # idx0_based: 0 for første element i ol (uavh. av start)
    start = int(ol.get("start", "1") or "1")
    base = (li_value if li_value is not None else (start + idx0_based))
    typ  = (ol.get("type") or "1")
    if typ in ("1", ""):
        return str(base)
    if typ == "a":
        return _alpha(base, upper=False)
    if typ == "A":
        return _alpha(base, upper=True)
    if typ == "i":
        return _roman(base, upper=False)
    if typ == "I":
        return _roman(base, upper=True)
    # ukjent type → bruk tall
    return str(base)

def _li_position(li: Tag) -> int:
    # 0-basert posisjon blant direkte <li>-søsken
    sibs = [x for x in li.parent.find_all("li", recursive=False)]
    try:
        return sibs.index(li)
    except ValueError:
        return 0

def _build_number_path(li: Tag) -> list[str]:
    """
    Bygg nummersti oppover for nested <ol>: f.eks. [ '1', '1' ] for 1.1
    Stopper ved første ikke-<ol>-forelder.
    """
    parts = []
    node = li
    while node is not None and getattr(node, "name", None) == "li":
        ol = node.parent if getattr(node.parent, "name", "") == "ol" else None
        if not ol:
            break
        idx0 = _li_position(node)
        li_val = None
        try:
            li_val = int(node.get("value")) if node.has_attr("value") else None
        except Exception:
            li_val = None
        parts.append(_ol_token_for_index(ol, idx0, li_val))
        # gå videre opp: finn li som inneholder denne ol-en (nested list)
        # dvs: node = ancestor li som er forelder til ol
        anc = ol.parent
        while anc is not None and getattr(anc, "name", None) != "li":
            anc = anc.parent
        node = anc
    return list(reversed(parts))

def _trailing_uc_letter_from_li(li: Tag) -> str | None:
    """
    Hvis selve teksten i li starter med en enkelt stor bokstav (A, B, …, Æ/Ø/Å),
    returner den, ellers None. (For å støtte '1.1 U'.)
    Vi *fjerner ikke* denne fra innholdet (konservativt).
    """
    # finn første betydelige tekst i li (uten å gå inn i nested lister/section)
    for child in li.find_all(recursive=False):
        if getattr(child, "name", None) in {"ol","ul","section"}:
            continue
        txt = child.get_text(" ", strip=True) if isinstance(child, Tag) else ""
        if not txt and isinstance(child, NavigableString):
            txt = str(child).strip()
        if txt:
            m = _UC_LETTER_PREFIX_RX.match(txt)
            if m:
                return m.group(1)
            break
    return None

def _ensure_section_in_li(li: Tag, cls: str, soup) -> Tag:
    """
    Sørg for at første betydelige barn i li er <section class=cls>.
    Returner denne seksjonen.
    """
    first = None
    for c in li.contents:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        first = c
        break

    if isinstance(first, Tag) and first.name == "section" and cls in (first.get("class", []) or []):
        return first

    # Hvis første barn er section, men 'feil' klasse → beholde men justere klassen
    if isinstance(first, Tag) and first.name == "section":
        classes = set(first.get("class", []) or [])
        classes.discard("task"); classes.discard("key")
        classes.add(cls)
        first["class"] = list(classes)
        return first

    # Ellers: opprett section og flytt alt inn
    sec = soup.new_tag("section")
    sec["class"] = [cls]
    li.insert(0, sec)
    # flytt resten av innholdet inn i section
    # NB: må iterere over en kopi
    rest = [x for x in li.contents if x is not sec]
    for n in rest:
        sec.append(n.extract())
    return sec

def _ensure_heading_in_section(sec: Tag, label: str, soup):
    # dersom første barn er en heading → ikke gjør noe
    first = None
    for c in sec.contents:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        first = c
        break
    if isinstance(first, Tag) and _HEADING_RX.match(first.name or ""):
        return

    level = _nearest_heading_level(sec)
    h = soup.new_tag(f"h{level}")
    h.string = label
    sec.insert(0, h)

# --- Hjelpere for 2.6 ----------------------------------------------------

def _nearest_section(node: Tag, soup) -> Tag:
    anc = node
    while anc is not None and getattr(anc, "name", None) != "section":
        anc = anc.parent
    return anc or (soup.body or soup)

def _first_sig_child(tag: Tag):
    for c in tag.contents:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        return c
    return None

def _nearest_heading_level(node: Tag) -> int:
    """
    Velg overskriftsnivå relativt til kontekst (én under nærmeste heading).
    """
    anc = node
    while anc is not None:
        # se etter heading blant forelderens direkte barn FØR node
        cur = anc.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling
        # se etter heading direkte under anc
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 3

def _normalize_frame_classes(el: Tag):
    classes = set(el.get("class", []) or [])
    # behold bare gyldige ramme-klasser + andre eksisterende (ikke destruktivt),
    # men sørg for ramme/generisk-ramme-reglene
    has_bg = any(c.startswith("bg-") for c in classes)
    if has_bg:
        classes.add("ramme")
        classes.discard("generisk-ramme")
    else:
        # hvis ingen ramme-relaterte klasser → sett generisk-ramme
        if not (classes & {"ramme", "generisk-ramme"}):
            classes.add("generisk-ramme")
    el["class"] = sorted(classes)

def _skip_aside(aside: Tag) -> bool:
    et = (aside.get("epub:type") or "").lower()
    classes = set(aside.get("class", []) or [])
    if et == "z3998:production" or "prodnote" in classes or "fig-desc" in classes:
        return True
    if "glossary" in classes:
        return True
    if aside.find("dl"):  # glossaries håndteres i 2.4.4.x
        return True
    return False

# --- Hjelpere for 2.6.1 ----------------------------------------------------

#_HEADING_RX = re.compile(r"^h([1-6])$", re.I)

def _skip_math_aside(aside: Tag) -> bool:
    """Skipp prodnote/fig-desc/glossary/desc-lister som ikke skal konverteres her."""
    et = (aside.get("epub:type") or "").lower()
    classes = set(aside.get("class", []) or [])
    if et == "z3998:production" or "prodnote" in classes or "fig-desc" in classes:
        return True
    # Glossaries håndteres i 2.4.4.x
    if "glossary" in classes or aside.find("dl"):
        return True
    return False

def _nearest_heading_level(node: Tag) -> int:
    # Velg headingnivå relativt til kontekst (én under nærmeste heading), fallback h3
    anc = node
    while anc is not None:
        # se etter heading blant direkte barn før node
        cur = anc.previous_sibling
        while cur is not None:
            name = getattr(cur, "name", "") or ""
            m = _HEADING_RX.match(name)
            if m:
                return min(int(m.group(1)) + 1, 6)
            cur = cur.previous_sibling
        # se etter heading direkte under anc
        for child in anc.find_all(_HEADING_RX, recursive=False):
            m = _HEADING_RX.match(child.name)
            if m:
                return min(int(m.group(1)) + 1, 6)
        anc = anc.parent
    return 3

def _normalize_frame_classes(el: Tag):
    """Sørg for at boksene har riktig rammeklassestruktur."""
    classes = set(el.get("class", []) or [])
    has_bg = any(c.startswith("bg-") for c in classes)
    if has_bg:
        classes.add("ramme")
        classes.discard("generisk-ramme")
    else:
        if not ({"ramme", "generisk-ramme"} & classes):
            classes.add("generisk-ramme")
    el["class"] = sorted(classes)

# --- Hjelpere for 2.7 ----------------------------------------------------

def _tokenize_types(val: str) -> set[str]:
    return set((val or "").lower().replace(";", " ").replace(",", " ").split())

def _is_task_tag(tag: Tag) -> bool:
    return bool(_epub_types(tag) & _TASKISH_TOKENS)

def _nearest_section(tag: Tag, soup):
    anc = tag
    while anc is not None and getattr(anc, "name", None) != "section":
        anc = anc.parent
    return anc

def _find_insertion_point_end_of_text(section: Tag):
    """
    Returner noden vi skal sette *før* for å lande «på slutten av teksten»,
    men fortsatt før oppgaver/glossary/relokerte figurer. None = append på slutten.
    """
    children = [c for c in section.children if isinstance(c, Tag)]
    stop_idx = None
    for i, c in enumerate(children):
        if _is_task_tag(c):
            stop_idx = i; break
        if c.name == "aside" and (
            "glossary" in (c.get("class", []) or []) or c.get("data-relocated") == "dl-glossary"
        ):
            stop_idx = i; break
        if c.name == "figure" and c.get("data-relocated-figure") == "true":
            stop_idx = i; break
    if stop_idx is None:
        return None
    return children[stop_idx]

def _is_lightweight(tag: Tag) -> bool:
    """Heuristikk: korte tekstbokser uten tunge blokkelementer → ofte margkommentarer."""
    if not tag: return False
    cls = set(tag.get("class", []) or [])
    if "prodnote" in cls or "fig-desc" in cls or "glossary" in cls:
        return False
    tks = _epub_types(tag)
    if "z3998:production" in tks:
        return False
    if tag.find(["table","dl","figure","section"]):
        return False
    txt = tag.get_text(" ", strip=True)
    return bool(txt) and len(txt) <= 400

def _looks_like_margin_comment(tag: Tag) -> bool:
    if not isinstance(tag, Tag):
        return False
    if tag.get("data-processed") == "margin-comment":
        return False
    if tag.name not in {"aside", "div"}:
        return False
    cls = {c.lower() for c in (tag.get("class", []) or [])}
    tks = _epub_types(tag)
    has_hint = bool(cls & _MARGIN_CLASS_TOKENS) or bool(tks & _MARGIN_TYPE_TOKENS)
    return has_hint or _is_lightweight(tag)

def _extract_anchor_id_from_comment(tag: Tag | None) -> str | None:
    """
    Returner id (uten '#') hvis margkommentaren peker på et mål i teksten.
    Robust mot None / ikke-Tag / liste-attributter / uventede noder.
    """
    # Hard guard
    if tag is None or not isinstance(tag, Tag):
        return None

    def _first_str(val):
        if val is None:
            return None
        # Når BeautifulSoup gir lister for enkelte attributter
        if isinstance(val, (list, tuple)):
            for x in val:
                s = str(x).strip()
                if s:
                    return s
            return None
        return str(val).strip()

    # 1) Direkte koblingsattributter som kan peke på id
    for attr in ("data-ref", "data-for", "data-target", "aria-describedby"):
        try:
            v = _first_str(tag.attrs.get(attr))
            if v:
                if v.startswith("#"):
                    v = v[1:]
                if v:
                    return v
        except Exception:
            # ignorer uvanlig struktur
            pass

    # 2) Første <a href="#..."> inne i boksen
    try:
        a = tag.find("a", href=True)
        if a:
            href = _first_str(a.attrs.get("href"))
            if href and href.startswith("#"):
                return href[1:]
    except Exception:
        pass

    return None

def _ensure_ul_container(soup, anchor_or_section: Tag) -> Tag:
    """
    Finn/lag <ul class="margin-comments list-unstyled"> på riktig sted:
    - hvis anchor er en konkret node i teksten: sett UL *etter* ankeret,
    - ellers: helt på slutten av seksjonen, men før tasks/glossary/relokert.
    """
    if anchor_or_section is None or not isinstance(anchor_or_section, Tag):
        parent = getattr(soup, "body", None)
        if parent is None:
            ul = soup.new_tag("ul")
            ul["class"] = ["margin-comments", "list-unstyled"]
            return ul
        anchor_or_section = parent

    if getattr(anchor_or_section, "name", None) != "section":
        # Sett etter anker-node
        try:
            nxt = anchor_or_section.next_sibling
            while isinstance(nxt, NavigableString) and not nxt.strip():
                nxt = nxt.next_sibling
            if isinstance(nxt, Tag) and nxt.name == "ul" and "margin-comments" in (nxt.get("class", []) or []):
                return nxt
            ul = soup.new_tag("ul")
            ul["class"] = ["margin-comments", "list-unstyled"]
            anchor_or_section.insert_after(ul)
            return ul
        except Exception:
            # Fallback: legg i slutten av nærmeste seksjon
            sec = _nearest_section(anchor_or_section, soup) or soup.body
            if sec is None:
                ul = soup.new_tag("ul")
                ul["class"] = ["margin-comments", "list-unstyled"]
                return ul
            ref = _find_insertion_point_end_of_text(sec)
            ul = soup.new_tag("ul")
            ul["class"] = ["margin-comments", "list-unstyled"]
            (sec.append if ref is None else ref.insert_before)(ul)
            return ul

    # Seksjon: plasser ved end-of-text
    section = anchor_or_section
    ref = _find_insertion_point_end_of_text(section)

    # Finn eksisterende UL i end-of-text-sonen
    candidate = None
    if ref is None:
        last = None
        for c in section.contents[::-1]:
            if isinstance(c, Tag):
                last = c; break
        if last is not None and last.name == "ul" and "margin-comments" in (last.get("class", []) or []):
            candidate = last
    else:
        prev = ref.previous_sibling
        while isinstance(prev, NavigableString) and not prev.strip():
            prev = prev.previous_sibling
        if isinstance(prev, Tag) and prev.name == "ul" and "margin-comments" in (prev.get("class", []) or []):
            candidate = prev

    if candidate:
        return candidate

    ul = soup.new_tag("ul")
    ul["class"] = ["margin-comments", "list-unstyled"]
    if ref is None:
        section.append(ul)
    else:
        ref.insert_before(ul)
    return ul

def _comment_to_li(soup, box: Tag) -> Tag:
    """
    Konverter en boks til ett <li>. Behold eksisterende <p>-er hvis de finnes,
    ellers bruk samlet tekst.
    """
    li = soup.new_tag("li")
    ps = box.find_all("p", recursive=False)
    if ps and any(p.get_text("", strip=True) for p in ps):
        for p in list(ps):
            li.append(p.extract())
    else:
        txt = box.get_text(" ", strip=True)
        if txt:
            li.append(NavigableString(txt))
    return li

# --- Hjelpere for § 2.8.1 -----------------------------------------------------
# ------------------------------- Hjelpere -------------------------------------


'''
def _nearest_section(node: Tag):
    anc = node
    while anc is not None and getattr(anc, "name", None) != "section":
        anc = anc.parent
    return anc
'''

def _mark_section_as_play(section: Tag):
    if not section or section.name != "section":
        return
    cls = set(section.get("class", []) or [])
    if "play" not in cls:
        cls.add("play")
        section["class"] = sorted(cls)

def _valid_speaker_name(name: str) -> bool:
    """Streng validering for å unngå matte/etikett-feller."""
    if not name:
        return False
    n = name.strip().strip(" .-–—").lower()
    if n in _STOPNAME_TOKENS:
        return False
    if len(n) <= 1:
        return False
    # Ikke tillat tall/likhetstegn/typiske formeltegn i «navn»
    if any(ch.isdigit() for ch in n) or any(ch in "=±×·*/^" for ch in n):
        return False
    # Krev minst én vokal (filtrerer "V:", "MN:" osv.)
    return bool(re.search(r"[aeiouyæøå]", n, flags=re.I))

def _is_entirely_italic_p(p: Tag) -> bool:
    """Hele avsnittet er kursiv (klassisk regianvisning)."""
    if p is None or p.name != "p":
        return False
    content = [c for c in p.contents if not (isinstance(c, NavigableString) and not c.strip())]
    if len(content) != 1:
        return False
    child = content[0]
    return isinstance(child, Tag) and child.name in {"em","i"} and not child.find(True)

def _looks_like_stage_direction_text(text: str) -> bool:
    """Parenteslinje eller kort regiaktig tekst uten dialog-cue."""
    if not text:
        return False
    t = text.strip()
    if len(t) <= 240 and t.startswith("(") and t.endswith(")"):
        return True
    if len(t) <= 120 and not _SPEAKER_RX.match(t or ""):
        low = t.lower()
        if any(tok in low for tok in ("(","exit","pause","stille","banker","sukker","ser","går","trår","roper")):
            return True
    return False

def _wrap_speaker_span_in_p(soup, p: Tag, match: re.Match) -> bool:
    """Pakk talerens navn i <span class="speaker">…: </span> (idempotent)."""
    # Ikke rør hvis allerede pakket
    first_el = next((c for c in p.contents if not (isinstance(c, NavigableString) and not c.strip())), None)
    if isinstance(first_el, Tag) and first_el.name == "span" and "speaker" in (first_el.get("class", []) or []):
        return False

    # Finn første tekstnode (løft enkel inline om nødvendig)
    first_text_idx = None
    for idx, c in enumerate(p.contents):
        if isinstance(c, NavigableString) and str(c):
            first_text_idx = idx; break
        if isinstance(c, Tag) and c.name in {"em","strong","b","i","span"} and c.get_text("", strip=False) and not c.find(True):
            c.replace_with(NavigableString(c.get_text("", strip=False)))
            first_text_idx = idx; break
    if first_text_idx is None:
        return False

    text_node = p.contents[first_text_idx]
    txt = str(text_node)
    m = _SPEAKER_RX.match(txt)
    if not m:
        return False

    raw_name = m.group(1).strip()
    if not _valid_speaker_name(raw_name):
        return False

    delim = m.group(2)
    span = soup.new_tag("span"); span["class"] = ["speaker"]
    span.append(f"{raw_name}{delim} ")
    rest = txt[m.end():]

    text_node.replace_with(span)
    if rest:
        span.insert_after(NavigableString(rest))
    return True

def _section_has_play_cues(section: Tag) -> bool:
    """
    Krev sterke signaler før vi gjør noe:
    - eksplisitt class='play' eller epub:type med 'drama'/'play', ELLER
    - heading med play-ord, ELLER
    - >=6 replikk-linjer og >=2 ulike talernavn, ELLER
    - >=3 replikk-linjer + >=2 regilinjer.
    """
    if not section or section.name != "section":
        return False

    et = (section.get("epub:type") or "").lower()
    if "drama" in et or "play" in et:
        return True
    if "play" in (section.get("class", []) or []):
        return True

    # Heading-cue
    head_text = None
    for child in section.find_all(_HEADING_RX, recursive=False):
        head_text = child.get_text(" ", strip=True).lower()
        break
    if head_text and any(tok in head_text for tok in _PLAY_HEADING_TOKENS):
        return True

    # Statistikk i seksjonen
    speaker_lines = 0
    name_counts = {}
    stage_dirs = 0
    for p in section.find_all("p"):
        t = p.get_text("", strip=False)
        m = _SPEAKER_RX.match(t or "")
        if m and _valid_speaker_name(m.group(1)):
            speaker_lines += 1
            key = m.group(1).strip().lower()
            name_counts[key] = name_counts.get(key, 0) + 1
        elif "directions" in (p.get("class", []) or []):
            stage_dirs += 1
        elif _is_entirely_italic_p(p) or _looks_like_stage_direction_text(t or ""):
            stage_dirs += 1

    distinct_names = sum(1 for _n, c in name_counts.items() if c >= 1)
    if speaker_lines >= 6 and distinct_names >= 2:
        return True
    if speaker_lines >= 3 and stage_dirs >= 2:
        return True
    return False

# ----------------------------- Cleanup-pass -----------------------------------

def cleanup_false_play_markup(soup, logger):
    """
    Rydd opp falske positiver fra tidligere kjøringer:
    - Avpakk gale <span class="speaker">…</span> (bevar råtekst).
    - Fjern 'directions' fra vanlige avsnitt.
    - Demoter/fjern 'class="play"' der seksjonen ikke har genuine drama-cues.
    - Fjern auto-lagde play-seksjoner (data-auto-play="true") uten drama-cues.
    """
    fixed = removed_play = 0

    # 1) Avpakk gale 'speaker'
    for span in list(soup.find_all("span", class_="speaker")):
        raw = (span.get_text("", strip=False) or "")
        name = raw.rstrip(":–—- ").strip()
        if not _valid_speaker_name(name):
            span.replace_with(NavigableString(raw))
            fixed += 1

    # 2) Fjern gale 'directions'
    for p in list(soup.find_all("p", class_=lambda cs: cs and "directions" in cs)):
        txt = p.get_text("", strip=False) or ""
        if not _is_entirely_italic_p(p) and not _looks_like_stage_direction_text(txt):
            classes = set(p.get("class", []) or [])
            classes.discard("directions")
            if classes:
                p["class"] = sorted(classes)
            elif "class" in p.attrs:
                del p["class"]
            fixed += 1

    # 3) Demoter seksjoner med class="play" uten solide cues
    def _section_has_real_drama(sec: Tag) -> bool:
        speakers = 0; names = {}; dirs = 0
        for p in sec.find_all("p"):
            t = p.get_text("", strip=False) or ""
            m = _SPEAKER_RX.match(t)
            if m and _valid_speaker_name(m.group(1)):
                speakers += 1
                key = m.group(1).strip().lower()
                names[key] = names.get(key, 0) + 1
            elif "directions" in (p.get("class", []) or []):
                dirs += 1
            elif _is_entirely_italic_p(p) or _looks_like_stage_direction_text(t):
                dirs += 1
        distinct = sum(1 for _n, c in names.items() if c >= 1)
        return (speakers >= 3 and distinct >= 2) or (speakers >= 2 and dirs >= 2)

    for sec in list(soup.find_all("section", class_="play")):
        if not _section_has_real_drama(sec):
            cls = set(sec.get("class", []) or [])
            if "play" in cls:
                cls.remove("play")
                if cls:
                    sec["class"] = sorted(cls)
                else:
                    if "class" in sec.attrs:
                        del sec["class"]
                removed_play += 1

        # Fjern auto-play-seksjon hvis den likevel ikke er drama
        if sec.get("data-auto-play") == "true" and not _section_has_real_drama(sec):
            for child in list(sec.contents):
                sec.insert_before(child.extract())
            sec.decompose()
            removed_play += 1

    logger.info("Cleanup §2.8.1: unwrapped_speaker/directions=%d, demoted/removed_play=%d",
                fixed, removed_play)
    return soup

# --- Hjelpere for § 2.9 -----------------------------------------------------
# OBS: <body> og <html> håndteres som blokknivå i praksis
def _is_block(tag: Tag) -> bool:
    if not getattr(tag, "name", None):
        return False
    n = tag.name.lower()
    return n in _BLOCK_TAGS or n in {"body","html"}


def _ensure_unique_id(soup, base_id: str) -> str:
    """Gjør id unik ved å suffikse -2, -3, ... om nødvendig."""
    if not base_id:
        return base_id
    if soup.find(id=base_id) is None:
        return base_id
    # base_id finnes allerede – finn neste ledige
    i = 2
    while soup.find(id=f"{base_id}-{i}") is not None:
        i += 1
    return f"{base_id}-{i}"

def _normalize_pagebreak_tag(pb: Tag):
    """Tving pagebreak til div + riktige attributter; fjern innhold."""
    # alltid <div>
    pb.name = "div"
    # epub:type skal inneholde pagebreak (bevar ev. andre tokens)
    et = (pb.get("epub:type") or "").strip()
    tokens = set(et.split()) if et else set()
    tokens.add("pagebreak")
    pb["epub:type"] = " ".join(sorted(tokens))
    # role
    if pb.get("role") != "doc-pagebreak":
        pb["role"] = "doc-pagebreak"
    # tomt innhold
    for c in list(pb.contents):
        c.extract()

def _label_from_existing(pb: Tag) -> str | None:
    return pb.get("aria-label") or pb.get("title")

def _maybe_set_label_from_id(pb: Tag):
    """Hvis ingen aria-label/title, og id inneholder tall, bruk det som aria-label."""
    if _label_from_existing(pb):
        return
    pid = pb.get("id") or ""
    m = re.search(r"\d+", pid)
    if m:
        pb["aria-label"] = m.group(0)

def _move_pagebreak_out_of_p(soup, pb: Tag) -> bool:
    """
    Når pagebreak ligger inne i <p>:
    - Del <p> i 'før' og 'etter'.
    - Behold 'før' i eksisterende <p>, sett pagebreak etter <p>,
      og opprett et nytt <p> for 'etter' (om nødvendig).
    """
    p = pb.parent
    if not (p and getattr(p, "name", "").lower() == "p"):
        return False

    # Del opp innholdet i p i noder før/etter pb
    before_nodes, after_nodes = [], []
    in_after = False
    for node in list(p.contents):
        if node is pb:
            in_after = True
            continue
        (after_nodes if in_after else before_nodes).append(node)

    # Tøm <p> og fyll tilbake 'før'-noder
    p.clear()
    for n in before_nodes:
        # n er allerede løsrevet etter clear(); bare legg det inn
        p.append(n)

    # Trekk pb ut og sett mellom 'før' og 'etter'
    pb.extract()
    p.insert_after(pb)

    # Lag nytt <p> med 'etter'-noder hvis det er innhold
    has_after_content = any(
        (isinstance(n, Tag) and (n.name or n.find(True) or n.get_text("", strip=True))) or
        (isinstance(n, NavigableString) and str(n).strip())
        for n in after_nodes
    )
    if has_after_content:
        new_p = soup.new_tag("p")
        for n in after_nodes:
            new_p.append(n)
        pb.insert_after(new_p)

    # Hvis 'før' er helt tomt (pb sto først), fjern tomt <p>
    if not p.find(True) and not p.get_text("", strip=True):
        p.decompose()

    return True

def _move_pagebreak_to_block_level(pb: Tag):
    """
    Hvis parent er inline (ikke-block), flytt pagebreak opp til nærmeste blokknivå
    ved å plassere den rett etter den laveste inline-forfaderen.
    """
    parent = pb.parent
    if not parent:
        return
    # Hvis allerede direkte under en block, er det ok (unntatt <p> som håndteres separat)
    if _is_block(parent) and parent.name.lower() != "p":
        return

    # Finn nærmeste forfader som er block
    inline_ancestor = pb
    block_ancestor = parent
    while block_ancestor and not _is_block(block_ancestor):
        inline_ancestor = block_ancestor
        block_ancestor = block_ancestor.parent

    # Ekstrakt pb og legg inn *etter* inline_ancestor på block-nivå
    pb.extract()
    # Hvis vi ikke fant block_ancestor, bare append til body/html
    if not block_ancestor:
        # nødløsning: bare plasser etter inline_ancestor i dets parent
        inline_ancestor.insert_after(pb)
        return

    # Sett inn etter inline_ancestor (bevarer relativ posisjon best mulig)
    inline_ancestor.insert_after(pb)

# --- Hjelpere for § 2.9.1 -----------------------------------------------------

def _first_sig_child(tag: Tag):
    for c in tag.contents:
        if isinstance(c, NavigableString) and not c.strip():
            continue
        return c
    return None

def _next_sig_sibling(tag: Tag):
    sib = tag.next_sibling
    while sib is not None and isinstance(sib, NavigableString) and not str(sib).strip():
        sib = sib.next_sibling
    return sib

def _prev_sig_sibling(tag: Tag):
    sib = tag.previous_sibling
    while sib is not None and isinstance(sib, NavigableString) and not str(sib).strip():
        sib = sib.previous_sibling
    return sib

def _first_heading_child(section: Tag):
    for c in section.contents:
        if isinstance(c, Tag) and _HEADING_RX.match(c.name or ""):
            return c
    return None

def _is_list(tag: Tag) -> bool:
    return bool(tag and getattr(tag, "name", "").lower() in {"ol","ul"})

def _is_li(tag: Tag) -> bool:
    return bool(tag and getattr(tag, "name", "").lower() == "li")

def _is_section(tag: Tag) -> bool:
    return bool(tag and getattr(tag, "name", "").lower() == "section")

def _move_pagebreak_out_of_p_safe(soup, pb: Tag) -> bool:
    """Bruker split-funksjonen fra § 2.9 dersom pb fremdeles ligger i <p>."""
    p = pb.parent
    if not (p is not None and getattr(p, "name", "").lower() == "p"):
        return False
    # Gjenbruk fiks fra §2.9 (pass soup inn):
    return _move_pagebreak_out_of_p(soup, pb)

def _relocate_pagebreak_in_lists(pb: Tag) -> bool:
    """
    Plasser pagebreak ved slutten av siste <li> på forrige side:
    - Hvis pb ligger *inni* et <li> → flytt til etter forrige <li> (eller før lista om ingen forrige).
    - Hvis pb er direkte barn av <ol>/<ul>:
      - Hvis den står *før* første <li> → flytt *før* lista.
      - Ellers la den stå (den er allerede mellom <li>’er).
    """
    # Finn nærmeste li-ancestor
    li_anc = pb.find_parent("li")
    if li_anc is not None:
        prev_li = li_anc.find_previous_sibling("li")
        pb.extract()
        if prev_li is not None:
            prev_li.insert_after(pb)   # mellom prev_li og li_anc
        else:
            # først i lista → plasser pagebreak før lista
            lst = li_anc.parent
            lst.insert_before(pb)
        return True

    # Hvis pb ligger direkte i lista (mellom <li>)
    parent = pb.parent
    if _is_list(parent):
        prev = _prev_sig_sibling(pb)
        if not (_is_li(prev)):
            # pb står før første li → flytt *før* lista
            pb.extract()
            parent.insert_before(pb)
            return True
        # ellers er den allerede mellom li-ene (ok)
        return False

    # pb ligger ikke i en liste
    return False

def _relocate_pagebreak_at_section_start(soup, pb: Tag) -> bool:
    """
    Der pagebreak ved start av *ny* <section> skal ligge:
    - Mellom <section>-start og headingen i den nye seksjonen.
    Håndterer tre tilfeller:
    1) pb ligger som *forrige søsken* til en <section> → flytt inn foran heading.
    2) pb ligger som *siste barn* i forrige <section> → flytt til neste <section> før heading.
    3) pb ligger *i* ny <section> men *etter* heading → flytt *før* heading.
    """
    moved = False

    # (1) pb rett før en section-søster
    nxt = _next_sig_sibling(pb)
    if _is_section(nxt):
        head = _first_heading_child(nxt)
        pb.extract()
        if head is not None:
            head.insert_before(pb)
        else:
            # ingen heading → først i seksjonen
            first = _first_sig_child(nxt)
            if first is not None:
                first.insert_before(pb)
            else:
                nxt.append(pb)
        return True

    # (2) pb ligger som siste i en seksjon, og neste søsken er ny seksjon
    par = pb.parent
    if _is_section(par):
        after_pb = _next_sig_sibling(pb)
        if after_pb is None:
            # pb er (siste) i seksjon; se om neste søsken til seksjonen er en ny seksjon
            next_section = _next_sig_sibling(par)
            if _is_section(next_section):
                head = _first_heading_child(next_section)
                pb.extract()
                if head is not None:
                    head.insert_before(pb)
                else:
                    first = _first_sig_child(next_section)
                    if first is not None:
                        first.insert_before(pb)
                    else:
                        next_section.append(pb)
                return True

    # (3) pb ligger *inne i* en seksjon, men etter headingen → flytt foran heading
    sec = pb.find_parent("section")
    if sec is not None:
        head = _first_heading_child(sec)
        if head is not None:
            # sjekk om pb står før headingen allerede
            cur = _first_sig_child(sec)
            if cur is head and pb is not head:
                # første barn er heading → pb står ikke først
                pb.extract()
                head.insert_before(pb)
                return True
            # pb etter heading? Flytt
            # robust: hvis pb kommer etter heading i traverseringsrekkefølge, flytt
            came_after = False
            for el in sec.descendants:
                if el is head:
                    came_after = False
                if el is pb:
                    came_after = True
                    break
            # Liten heuristikk: hvis pb er søsken etter heading
            if head.find_next(lambda t: t is pb) is not None:
                pb.extract()
                head.insert_before(pb)
                return True

    return moved

# --- Hjelpere for § 2.10 -----------------------------------------------------

def _is_header_row(tr: Tag) -> bool:
    """En rad regnes som 'thead'-rad hvis den har minst én celle og ALLE celler er <th>."""
    if getattr(tr, "name", "") != "tr":
        return False
    cells = [c for c in tr.find_all(["th", "td"], recursive=False)]
    return bool(cells) and all(c.name == "th" for c in cells)

def _assign_scopes(thead: Tag | None, tbody: Tag | None):
    # th i thead → scope="col"
    if thead:
        for th in thead.find_all("th"):
            if not th.has_attr("scope"):
                th["scope"] = "col"
    # th i tbody som første celle i en rad → scope="row"
    if tbody:
        for tr in tbody.find_all("tr", recursive=True):
            cells = [c for c in tr.find_all(["th", "td"], recursive=False)]
            if not cells:
                continue
            first = cells[0]
            if first.name == "th" and not first.has_attr("scope"):
                first["scope"] = "row"

# --- Hjelpere for § 2.10.1 -----------------------------------------------------

def _cell_span(cell: Tag) -> int:
    try:
        return max(1, int(cell.get("colspan", "1")))
    except Exception:
        return 1

def _row_effective_cols(tr: Tag) -> int:
    if getattr(tr, "name", "") != "tr":
        return 0
    return sum(_cell_span(c) for c in tr.find_all(["th","td"], recursive=False))

def _is_collapsed(cell: Tag) -> bool:
    st = (cell.get("style") or "").replace(" ", "").lower()
    # enkel heuristikk for 'flag cell' som er visuelt skjult
    return "visibility:collapse" in st or "display:none" in st

def _ensure_caption_node(soup, table: Tag) -> Tag:
    cap = table.find("caption", recursive=False)
    if cap is None:
        cap = soup.new_tag("caption")
        # sett inn foreløpig på topp; vi vil uansett sikre rekkefølgen senere
        table.insert(0, cap)
    return cap

def _move_caption_first(table: Tag):
    # Flytt caption til å være første direkte barn
    cap = table.find("caption", recursive=False)
    if not cap:
        return
    if cap.previous_sibling is None:
        return  # allerede først
    cap.extract()
    table.insert(0, cap)

# --- Hjelpere for § 2.10.2 -----------------------------------------------------

# Separatorer som ofte indikerer "flere elementer" stukket inn i én celle
_CELL_SEP_RX = re.compile(r'\s*(?:,|;|/|\||•|·|–|-)\s+')

def _has_math(node: Tag) -> bool:
    # Ikke rør celler som inneholder MathML, AsciiMath, eller LaTeX-fragmenter
    if node.find('math'):
        return True
    classes = ' '.join(node.get('class', [])).lower()
    if 'asciimath' in classes:
        return True
    # very light LaTeX heuristic
    txt = node.get_text('', strip=True)
    if '$' in txt or r'\(' in txt or r'\[' in txt:
        return True
    return False

def _split_by_br(node: Tag) -> list[str]:
    """Del innhold i cellen ved <br>-grenser, bevar tekst (strippet)."""
    items = []
    buf = []
    for child in list(node.children):
        if isinstance(child, Tag) and child.name.lower() == 'br':
            text = ''.join(c if isinstance(c, str) else c.get_text(' ', strip=True) for c in buf).strip()
            if text:
                items.append(text)
            buf = []
        else:
            if isinstance(child, NavigableString):
                buf.append(str(child))
            elif isinstance(child, Tag):
                buf.append(child.get_text(' ', strip=True))
    # siste buffer
    text = ''.join(c if isinstance(c, str) else c for c in buf).strip()
    if text:
        items.append(text)
    return [i for i in (t.strip() for t in items) if i]

def _split_by_separators(text: str) -> list[str]:
    parts = _CELL_SEP_RX.split(text)
    return [p.strip() for p in parts if p and p.strip()]

def _looks_like_number_list(text: str) -> bool:
    # flere tall / tallområder separert av sep/whitespace
    nums = re.findall(r'(?:\b\d{1,3}(?:[.,]\d+)?\b)', text)
    return len(nums) >= 4  # terskel: minst 4 tall → sannsynlig liste

def _token_density(text: str) -> float:
    tokens = re.findall(r'\w+', text, flags=re.UNICODE)
    return len(tokens) / max(1, len(text))

def _is_suspicious_cell(cell: Tag) -> bool:
    if _has_math(cell):
        return False
    # Idempotens: hopp hvis vi allerede har normalisert til <ul class="list-unstyled">
    if cell.find('ul', class_='list-unstyled'):
        return False

    # <br>-tunge celler → sannsynlig liste
    if cell.find('br'):
        parts = _split_by_br(cell)
        if len(parts) >= 3:
            return True

    text = cell.get_text(' ', strip=True)
    if not text or len(text) < 6:
        return False

    # Mange separatorer → sannsynlig liste
    if len(re.findall(_CELL_SEP_RX, text)) >= 3:
        return True

    # Tall-liste?
    if _looks_like_number_list(text):
        return True

    # Uvanlig høy tokendensitet kan indikere manglende cellegrenser (konservativ)
    if _token_density(text) > 0.25 and len(text) > 120 and len(text.split()) > 25:
        return True

    return False

def _normalize_cell_to_ul(cell: Tag, soup, logger) -> bool:
    if cell.find('ul', class_='list-unstyled'):
        return False
    parts = []
    if cell.find('br'):
        parts = _split_by_br(cell)
    if not parts:
        text = cell.get_text(' ', strip=True)
        parts = _split_by_separators(text)
        if len(parts) < 3:
            return False

    # Terskler: unngå å lage gigantiske lister utilsiktet
    if len(parts) > 50:
        logger.debug("2.10.2 - Suspicious cell has >50 items; skipping auto-normalization.")
        return False

    # Tøm cellen og bygg ul
    for n in list(cell.contents):
        n.extract()
    ul = soup.new_tag('ul', attrs={'class': 'list-unstyled'})
    for p in parts:
        li = soup.new_tag('li')
        li.string = p
        ul.append(li)
    cell.append(ul)
    return True

# --- Hjelpere for § 2.10.4 -----------------------------------------------------

def _has_math_content(tag):
    if tag.find("math"):
        return True
    classes = " ".join(tag.get("class", [])).lower()
    if "asciimath" in classes:
        return True
    txt = tag.get_text("", strip=True)
    if "$" in txt or r"\(" in txt or r"\[" in txt:
        return True
    return False

def _has_block_descendants(tag):
    for d in tag.descendants:
        if getattr(d, "name", None) in _BLOCK_TAGS and d is not tag:
            # tillat <br> (inline)
            if d.name == "br":
                continue
            return True
    return False

def _p_has_significant_attrs(p):
    # behold p hvis den har meningsfulle attributter som vi ikke vil miste
    if p.attrs:
        # noen ganger kommer tom class/id/style – filtrer på faktiske verdier
        for k, v in p.attrs.items():
            if v not in (None, "", [], {}):
                return True
    return False

def _cell_direct_ps(cell):
    # direkte-barn <p> (ikke dype)
    return [c for c in cell.find_all("p", recursive=False)]

def _collapse_consecutive_br(cell):
    prev_br = False
    for node in list(cell.children):
        if getattr(node, "name", "") == "br":
            if prev_br:
                node.decompose()
            prev_br = True
        elif isinstance(node, str) and not node.strip():
            # ignorer blanktekst ift. br-samling
            continue
        else:
            prev_br = False

# --- Hjelpere for § 2.10.5 -----------------------------------------------------

def _has_math(tag):
    if tag.find("math"):
        return True
    cls = " ".join(tag.get("class", [])).lower()
    if "asciimath" in cls:
        return True
    txt = tag.get_text("", strip=True)
    if "$" in txt or r"\(" in txt or r"\[" in txt:
        return True
    return False

def _li_direct_ps(li):
    return [c for c in li.find_all("p", recursive=False)]

def _unwrap_single_p_if_simple(li):
    """Unwrapper én enkel <p> når den er eneste innholdet i <li> og uten 'tunge' attrs/blocks."""
    ps = _li_direct_ps(li)
    # Ikke unwrap hvis andre blokker er direkte barn av li
    other_blocks = [c for c in li.children
                    if getattr(c, "name", None) not in (None, "p") and c.name in {
                        "address","article","aside","blockquote","canvas","div","dl","fieldset",
                        "figcaption","figure","footer","form","h1","h2","h3","h4","h5","h6",
                        "header","hr","li","main","nav","noscript","ol","pre","section",
                        "table","tbody","thead","tfoot","tr","th","td","ul"
                    }]
    if len(ps) == 1 and not other_blocks:
        p = ps[0]
        if not p.attrs and not p.find(True):
            # flytt ren tekst/inline ut
            for n in list(p.contents):
                p.insert_before(n.extract())
            p.decompose()
            return True
    return False

def _merge_multi_p_with_br(li, soup):
    """Slå sammen flere <p> til tekst med <br>, hvis det ikke finnes andre blokker."""
    ps = _li_direct_ps(li)
    if len(ps) < 2:
        return False
    # Ikke rør om li har andre blokker direkte (lister, figurer, tabeller, osv)
    other_blocks = [c for c in li.children if getattr(c, "name", None) not in (None, "p")]
    if other_blocks:
        return False
    # Ikke slå sammen hvis noen p har blokkelementer inni
    for p in ps:
        if p.find(True):
            return False
    # Merge
    for i, p in enumerate(ps):
        for n in list(p.contents):
            p.insert_before(n.extract())
        if i < len(ps) - 1:
            p.insert_before(soup.new_tag("br"))
        p.decompose()
    return True

def _strip_leading_bullet_in_li(li):
    """Fjern synlig kule/dash i starten av første tekst i <li>. Returnerer True om noe ble fjernet."""
    # Finn første NavigableString eller tekstnær node
    for node in li.contents:
        if isinstance(node, NavigableString):
            m = _BULLET_RX.match(str(node))
            if m:
                node.replace_with(_BULLET_RX.sub("", str(node), count=1))
                return True
        elif getattr(node, "name", None):
            # hvis node er f.eks. <span>tekst…</span> som starter med kule
            t = node.get_text("", strip=False)
            m = _BULLET_RX.match(t)
            if m and node.string is not None:
                node.string.replace_with(_BULLET_RX.sub("", t, count=1))
                return True
        # stopp ved første ikke-tomme innhold
        if (isinstance(node, NavigableString) and node.strip()) or getattr(node, "name", None):
            break
    return False

def _ul_needs_plain_class(ul):
    """Vurder om <ul> skal ha list-unstyled etter at synlige kuler er fjernet."""
    # Hvis ingen li lenger starter med kuletegn → plain
    for li in ul.find_all("li", recursive=False):
        # se råtekst for første tekstbit
        first_txt = li.get_text("", strip=False)
        if _BULLET_RX.match(first_txt):
            return False
    return True

def _mark_ol_nonstandard(ol):
    """Oppdag 'ikke-standard' nummerering (romersk, bokstav, blandet) og sett plain-klassene."""
    # Hvis type-attr allerede er a/A/i/I → plain
    t = (ol.get("type") or "").lower()
    if t in {"a","i"}:
        return True
    # Sjekk første par li for prefiksmønster
    lis = ol.find_all("li", recursive=False)[:4]
    hits = 0
    for li in lis:
        text = li.get_text(" ", strip=True)
        if _ROMAN_RX.match(text) or _ALPHA_RX.match(text):
            hits += 1
    return hits >= max(1, len(lis)//2)

def _ensure_class(dct, val):
    cls = set(dct.get("class", []) or [])
    if val not in cls:
        cls.add(val)
        dct["class"] = list(cls)

def _ensure_style_none(tag):
    style = (tag.get("style") or "").strip()
    if "list-style-type: none" not in style.replace(" ", "").lower():
        tag["style"] = (style + ("; " if style else "") + "list-style-type: none;").strip()


# --- Hjelpere for § 2.10.6 -----------------------------------------------------

def _norm_text(s: str | None) -> str:
    return (s or "").replace("\u00A0", " ").strip()

def _cell_is_empty(cell):
    # Har cellen “innhold” som må bevares? (da er den ikke tom)
    if cell.find(["img","svg","object","iframe","math","canvas","video","audio","picture","source"]):
        return False
    t = _norm_text(cell.get_text(" ", strip=True))
    return t in EMPTY_TOKENS

def _extract_caption_text(table):
    cap = table.find("caption")
    if cap:
        return cap.get_text(" ", strip=True)
    title = table.get("title")
    if title:
        return str(title).strip()
    return None

def _header_row_cells(table):
    # Foretrekk thead → første tr
    thead = table.find("thead")
    if thead:
        tr = thead.find("tr")
        return tr.find_all(["th","td"], recursive=False) if tr else []
    # Ellers: første rad som inneholder th
    for tr in table.find_all("tr"):
        cells = tr.find_all(["th","td"], recursive=False)
        if any(c.name == "th" for c in cells):
            return cells
    # Fallback: første rad
    tr = table.find("tr")
    return tr.find_all(["th","td"], recursive=False) if tr else []

def _col_headings(table):
    cells = _header_row_cells(table)
    out = []
    for c in cells:
        scope = (c.get("scope") or "").lower()
        if c.name == "th" or scope == "col":
            txt = _norm_text(c.get_text(" ", strip=True))
            if txt:
                out.append(txt)
    return out

def _row_headings(table, header_row=None):
    out = []
    rows = table.find_all("tr")
    for tr in rows:
        if header_row is not None and tr is header_row:
            continue
        cells = tr.find_all(["th","td"], recursive=False)
        if not cells:
            continue
        first = cells[0]
        scope = (first.get("scope") or "").lower()
        if first.name == "th" or scope == "row":
            txt = _norm_text(first.get_text(" ", strip=True))
            if txt:
                out.append(txt)
    return out

def _mk_ul_items(soup, items, cls):
    if not items:
        return None
    ul = soup.new_tag("ul")
    ul["class"] = ["list-unstyled", cls]
    for it in items:
        li = soup.new_tag("li")
        li.string = it
        ul.append(li)
    return ul

# --- Hjelpere for § 2.10.7 -----------------------------------------------------

# --- Hjelpere ---------------------------------------------------------------

def _has_complex_content(tag):
    # Ikke flate ut hvis tabellen inneholder “komplekst” innhold
    return bool(tag.find(["math","figure","img","svg","video","audio","object","canvas","iframe","dl","ol","ul"]))

def _cell_text(cell):
    return (cell.get_text(" ", strip=True) or "").replace("\u00A0", " ").strip()

def _is_numericish(s: str) -> bool:
    s = s.replace(",", ".")
    return bool(re.fullmatch(r"[+\-]?\d+(\.\d+)?([/%])?", s))

def _table_dims(table):
    rows = table.find_all("tr")
    n_rows = len(rows)
    n_cols = 0
    for tr in rows:
        cells = tr.find_all(["td","th"], recursive=False)
        n_cols = max(n_cols, len(cells))
    return n_rows, n_cols

def _row_cells(table):
    # liste av rader (som lister av celler)
    out = []
    for tr in table.find_all("tr"):
        out.append(tr.find_all(["td","th"], recursive=False))
    return out

def _row_is_header_like(cells):
    return all(c.name == "th" for c in cells) and len(cells) > 0

def _header_cells_first_row(table):
    tr = table.find("tr")
    if not tr:
        return []
    return [c for c in tr.find_all(["th","td"], recursive=False)
            if c.name == "th" or (c.get("scope") or "").lower() == "col"]

def _has_any_header(table):
    return bool(table.find("th"))

def _header_names(table):
    hdr = _header_cells_first_row(table)
    names = []
    for c in hdr:
        t = _cell_text(c)
        if t:
            names.append(t)
    return names

def _caption_text(table):
    cap = table.find("caption")
    if cap:
        return cap.get_text(" ", strip=True)
    title = table.get("title")
    if title:
        return (str(title) or "").strip()
    return None

def _estimate_layout_table(table):
    """
    Konservativ heuristikk for å avgjøre “layout vs data”.
    - 2–4 kolonner, moderat antall rader
    - få/enkle <th>
    - celler med korte tekster
    - lav andel rene tall
    - ikke ‘komplekst’ innhold
    """
    if _has_complex_content(table):
        return False, "complex-content"

    n_rows, n_cols = _table_dims(table)
    if n_cols < 2 or n_cols > 4:
        return False, "cols-out-of-range"
    if n_rows > 100:  # ytelses- og nøyaktighetshensyn
        return False, "too-many-rows"

    rows = _row_cells(table)
    total_cells = sum(len(r) for r in rows) or 1
    th_count = len(table.find_all("th"))
    th_ratio = th_count / total_cells

    texts = []
    numeric_hits = 0
    long_hits = 0
    for r in rows:
        for c in r:
            t = _cell_text(c)
            if t:
                texts.append(t)
                if _is_numericish(t):
                    numeric_hits += 1
                if len(t) > 40:
                    long_hits += 1

    text_cells = max(1, len(texts))
    numeric_ratio = numeric_hits / text_cells
    long_ratio = long_hits / text_cells

    header_ok = th_ratio <= 0.25
    numeric_ok = numeric_ratio <= 0.35
    long_ok = long_ratio <= 0.25
    size_ok = n_rows <= 25

    score = sum(int(x) for x in (header_ok, numeric_ok, long_ok, size_ok))
    if score >= 3:
        return True, "heuristics"
    return False, "heuristics-fail"

def _llm_agrees_layout(table, llm, logger):
    # Valgfri støtte for args.llm – kan være None hvis klient ikke finnes
    if not llm or not getattr(llm, "available", False):
        return None
    html_snip = str(table)[:3000]
    try:
        resp = llm.classify_table_layout(
            html_snippet=html_snip,
            hint="Decide if this HTML table is layout/styling-only or genuine data."
        )
        return bool(resp.get("layout", False))
    except Exception as e:
        logger.debug(f"2.10.7 - LLM classification failed: {e}")
        return None

def _make_ul_from_table(table, soup, use_headers=True):
    """
    Lager <ul class="list-unstyled table-as-list" data-2107="true">.
    - Hvis første rad er header → “Header: verdi; Header2: verdi2 …”
    - Ellers: “verdi1; verdi2; …”
    - Filtrerer tomme celler for å unngå ‘;;’
    """
    rows = _row_cells(table)
    if not rows:
        return None

    hdr_names = _header_names(table) if use_headers else []
    start_idx = 1 if rows and _row_is_header_like(rows[0]) else 0

    ul = soup.new_tag("ul")
    ul["class"] = ["list-unstyled", "table-as-list"]
    ul["data-2107"] = "true"

    for ri in range(start_idx, len(rows)):
        cells = rows[ri]
        vals = [_cell_text(c) for c in cells]
        # Filtrér bort tomme verdier før vi bygger LI
        vals = [v for v in vals if v]

        if not vals:
            continue

        li = soup.new_tag("li")

        if hdr_names and len(hdr_names) >= 2 and len(vals) >= 2:
            parts = []
            # Pakk sammen “Header: verdi”
            up_to = min(len(hdr_names), len(vals))
            for i in range(up_to):
                h = hdr_names[i]
                v = vals[i]
                if h and v:
                    parts.append(f"{h}: {v}")
                elif v:
                    parts.append(v)
            # ta med evt. overskytende verdier
            if len(vals) > up_to:
                parts.extend(vals[up_to:])
            text = "; ".join(parts).strip()
        else:
            text = "; ".join(vals).strip()

        # Ekstra sikkerhet: fjern evt. doble skilletegn hvis noe skulle glippe
        text = re.sub(r'\s*;\s*;\s*', '; ', text)
        li.string = text
        ul.append(li)

    return ul if ul.find("li") else None

# --- Hjelpere for § 2.10.7 -----------------------------------------------------

def _is_whitespace_node(n):
    from bs4 import NavigableString
    return isinstance(n, NavigableString) and not (str(n) or "").strip()

def _next_meaningful_sibling(node):
    sib = node.next_sibling
    while sib is not None and _is_whitespace_node(sib):
        sib = sib.next_sibling
    return sib

def _node_text(tag):
    return (tag.get_text(" ", strip=True) if hasattr(tag, "get_text") else "").strip()

def _looks_like_source_text(text: str) -> bool:
    if not text:
        return False
    if _SOURCE_PREFIX_RX.search(text):
        return True
    # Enkle signaturer: starter med © eller "Copyright"
    if text.startswith("©") or text.lower().startswith("copyright"):
        return True
    # Svært korte "— Forfatternavn" linjer etter blockquote tolkes ofte som kilde
    if text.startswith("—") and len(text) <= 120:
        return True
    return False

def _is_source_like_tag(tag) -> bool:
    if not getattr(tag, "name", None):
        return False
    if tag.name in {"cite"}:
        return True
    if tag.name in {"p", "small", "span", "div"}:
        return _looks_like_source_text(_node_text(tag))
    return False

def _ensure_llm(args, logger):
    try:
        if getattr(args, "llm", False):
            return _ensure_llm_client(logger, args.llm)
    except NameError:
        pass
    return None

def _llm_says_source(llm, container_html: str, candidate_text: str) -> bool | None:
    if not llm or not getattr(llm, "available", False):
        return None
    try:
        resp = llm.classify_is_source_line(
            html_context=container_html[:2000],
            candidate=candidate_text[:300]
        )
        return bool(resp.get("is_source", False))
    except Exception as e:
        logger.debug(f"2.11 - LLM classification failed: {e}")
        return None

def _append_cite_to_blockquote(bq, soup, content_tag):
    """Legg til <cite> inni blockquote av enten eksisterende <cite> eller plain tekst."""
    if content_tag.name == "cite":
        cite = content_tag
        cite.extract()
        bq.append(cite)
    else:
        text = _node_text(content_tag)
        cite = soup.new_tag("cite")
        cite.string = text
        bq.append(cite)
    bq["data-moved-source"] = "true"
    content_tag.decompose()

def _ensure_figcaption(fig, soup):
    cap = fig.find("figcaption")
    if cap is None:
        cap = soup.new_tag("figcaption")
        fig.append(cap)
    return cap

def _append_cite_to_figcaption(fig, soup, content_tag):
    cap = _ensure_figcaption(fig, soup)
    if content_tag.name == "cite":
        cite = content_tag
        cite["class"] = list(set(cite.get("class", [])) | {"source"})
        cite.extract()
        cap.append(cite)
    else:
        text = _node_text(content_tag)
        cite = soup.new_tag("cite")
        cite["class"] = ["source"]
        cite.string = text
        cap.append(cite)
    fig["data-moved-source"] = "true"
    content_tag.decompose()

def _ensure_caption(table, soup):
    cap = table.find("caption")
    if cap is None:
        cap = soup.new_tag("caption")
        table.insert(0, cap)
    else:
        # Sørg for at caption ligger først
        if cap is not table.contents[0]:
            cap.extract()
            table.insert(0, cap)
    return cap

def _append_source_to_caption(table, soup, content_tag):
    cap = _ensure_caption(table, soup)
    existing = _node_text(cap)
    if content_tag.name == "cite":
        src_text = _node_text(content_tag)
    else:
        src_text = _node_text(content_tag)

    if not src_text:
        # Ingen nytte → bare fjern kandidaten
        content_tag.decompose()
        return

    # Sett inn med ' – ' hvis vi allerede har caption-tekst
    if existing:
        cap.append(" – ")

    cite = soup.new_tag("cite")
    cite["class"] = ["source"]
    cite.string = src_text
    cap.append(cite)

    table["data-moved-source"] = "true"
    content_tag.decompose()

def _should_skip_target(el) -> bool:
    # Idempotens: ikke rør hvis vi allerede har flyttet kilde tidligere
    return el.get("data-moved-source") == "true"

# --- Hjelpere for § 2.12.1 -----------------------------------------------------

def _etokens(el: Tag) -> set:
    t = (el.get("epub:type") or "").lower().replace(";", " ").replace(",", " ")
    return set(t.split()) if t else set()

def _class_tokens(el: Tag) -> set:
    return set((el.get("class") or []))

def _role_token(el: Tag) -> str:
    return (el.get("role") or "").lower()

'''
def _nearest_section(node: Tag) -> Tag | None:
    p = node
    while p is not None:
        if getattr(p, "name", None) == "section":
            return p
        p = p.parent
    return soup.body or soup
'''

def _significant_children(parent: Tag):
    out = []
    for c in parent.contents:
        if isinstance(c, NavigableString) and not (str(c) or "").strip():
            continue
        out.append(c)
    return out

def _is_footnote_like(el: Tag) -> bool:
    if not getattr(el, "name", None):
        return False
    name = el.name.lower()
    et = _etokens(el)
    cls = _class_tokens(el)
    role = _role_token(el)
    if "footnote" in et or "endnote" in et:
        return True
    if role in {"doc-footnote", "doc-endnote"}:
        return True
    if name == "fn":
        return True
    if "footnote" in {c.lower() for c in cls}:
        return True
    # typiske containere for notelinjer
    if name in {"aside","div","li"} and ("fn" in cls or "notes" in cls):
        return True
    return False

def _belongs_to_footnote_list(el: Tag) -> Tag | None:
    """
    Hvis el er en del av en <ol>/<ul> med fotnoter, returner containeren (ellers None).
    """
    p = el.parent
    if isinstance(p, Tag) and getattr(p, "name", None) in {"ol","ul"}:
        pcl = {c.lower() for c in _class_tokens(p)}
        prole = _role_token(p)
        pet = _etokens(p)
        if ("footnotes" in pcl or prole in {"doc-endnotes","doc-footnotes"} or
            "footnotes" in pet or "endnotes" in pet):
            return p
    return None

def _at_end_of_section(container: Tag, node: Tag) -> bool:
    kids = _significant_children(container)
    if not kids:
        return False
    # node må være siste signifikante barn
    return kids and (kids[-1] is node)

def _ensure_llm(logger, args):
    try:
        if getattr(args, "llm", False):
            return _ensure_llm_client(logger, args.llm)
    except NameError:
        pass
    return None

def _llm_is_footnote(llm, context_html: str, candidate_text: str):
    if not llm or not getattr(llm, "available", False):
        return None
    try:
        resp = llm.classify_is_footnote(html_context=context_html[:2000],
                                        candidate=candidate_text[:300])
        return bool(resp.get("is_footnote", False))
    except Exception as e:
        logger.debug(f"2.12.1 - LLM classification failed: {e}")
        return None

def _node_text(tag: Tag) -> str:
    return (tag.get_text(" ", strip=True) if hasattr(tag, "get_text") else "").strip()


# --- Hjelpere for § 2.12.2 -----------------------------------------------------

def _end_tok(val: str) -> set[str]:
    return set((val or "").lower().replace(";", " ").replace(",", " ").split())

def _end_etokens(el: Tag) -> set[str]:
    return _end_tok(el.get("epub:type", ""))

def _end_class_tokens(el: Tag) -> set[str]:
    return set((el.get("class") or []))

def _end_role(el: Tag) -> str:
    return (el.get("role") or "").lower()

def _end_is_significant(n) -> bool:
    return not (isinstance(n, NavigableString) and not (str(n) or "").strip())

def _end_significant_children(parent: Tag):
    return [c for c in parent.contents if _end_is_significant(c)]

def _end_top_level_section(soup):
    # Finn toppnivå <section> i denne xhtml-fila (typisk første direkte barn av <body>)
    if soup.body:
        for ch in soup.body.children:
            if isinstance(ch, Tag) and ch.name == "section":
                return ch
    # fallback: første <section> hvor som helst
    sec = soup.find("section")
    return sec or soup.body or soup

def _end_is_endnotes_container(el: Tag) -> bool:
    if not getattr(el, "name", None):
        return False
    et = _end_etokens(el)
    cls = {c.lower() for c in _end_class_tokens(el)}
    role = _end_role(el)
    if "endnotes" in et or "chapter-notes" in et:
        return True
    if role in {"doc-endnotes"}:
        return True
    if "endnotes" in cls:
        return True
    # Vanlige varianter: <section class="notes"> med heading "Noter"/"Endnotes"
    if el.name in {"section","div"} and ("notes" in cls or "note" in cls):
        # Vi lar LLM/heuristikk ta en beslutning senere hvis nødvendig
        return False
    return False

def _end_is_single_endnote(el: Tag) -> bool:
    if not getattr(el, "name", None):
        return False
    name = el.name.lower()
    et = _end_etokens(el)
    cls = {c.lower() for c in _end_class_tokens(el)}
    role = _end_role(el)
    if name == "fn":
        return True
    if "endnote" in et:
        return True
    if role in {"doc-endnote"}:
        return True
    if "endnote" in cls:
        return True
    # <li id="en-1"> inne i en endnotes-liste – håndteres via containeren, ikke her
    return False

def _end_in_endnotes_container(el: Tag) -> Tag | None:
    p = el.parent
    if isinstance(p, Tag) and getattr(p, "name", None) in {"ol","ul","section","div"}:
        if _end_is_endnotes_container(p) or p.get("data-relocated-endnotes") == "true":
            return p
        # <ol class="endnotes"> …
        if p.name in {"ol","ul"}:
            pcl = {c.lower() for c in _end_class_tokens(p)}
            pet = _end_etokens(p)
            prole = _end_role(p)
            if ("endnotes" in pcl or "endnotes" in pet or prole in {"doc-endnotes"}):
                return p
    return None

def _end_already_at_end(container: Tag, node: Tag) -> bool:
    kids = _end_significant_children(container)
    return bool(kids) and kids[-1] is node

def _end_ensure_llm(logger, args):
    try:
        if getattr(args, "llm", False):
            return _ensure_llm_client(logger, args.llm)
    except Exception:
        pass
    return None

def _end_llm_is_endnotes_container(llm, context_html: str) -> bool | None:
    if not llm or not getattr(llm, "available", False):
        return None
    try:
        resp = llm.classify_is_endnotes_container(html_context=context_html[:2000])
        return bool(resp.get("is_endnotes_container", False))
    except Exception as e:
        logger.debug(f"2.12.2 - LLM classification failed: {e}")
        return None

# --- Hjelpere for § 2.13.1 -----------------------------------------------------


def _norm_label(s: str) -> str:
    s = (s or "").strip()
    s = s.replace(".", "").replace(":", "")
    s = s.strip("()[]{}⟨⟩")
    return s.upper()

def _cell_text(el: Tag) -> str:
    return " ".join(list(el.stripped_strings))

def _is_significant(n) -> bool:
    return not (isinstance(n, NavigableString) and not (str(n) or "").strip())

# --- Heuristikk: tabell-basert analyse -----------------------------------

def _looks_like_grammar_table(table: Tag) -> bool:
    rows = table.find_all("tr", recursive=False)
    if len(rows) < 2:
        return False
    top_cells = rows[0].find_all(["th","td"], recursive=False)
    if len(top_cells) < 2:
        return False
    labels = [_norm_label(_cell_text(c)) for c in top_cells]
    score = sum(1 for L in labels if L in _GRAM_LABELS)
    return score >= max(2, len(labels)//2)

def _table_to_bracketed_p(table: Tag, soup) -> Tag | None:
    rows = table.find_all("tr", recursive=False)
    if len(rows) < 2:
        return None
    top = rows[0].find_all(["th","td"], recursive=False)
    bot = rows[1].find_all(["th","td"], recursive=False)
    if not bot:
        return None

    labels = [_norm_label(_cell_text(c)) for c in top]
    words  = [_cell_text(c) for c in bot]

    if len(labels) < len(words) and any(labels):
        labels = labels + [""] * (len(words) - len(labels))
    elif len(labels) > len(words):
        labels = labels[:len(words)]

    out_segments: list[tuple[str|None, str]] = []
    cur_label: str | None = None
    cur_words: list[str] = []

    def flush():
        nonlocal cur_label, cur_words
        if cur_words:
            text = " ".join(w for w in cur_words if w)
            if text:
                out_segments.append((cur_label, text))
        cur_label, cur_words = None, []

    for i in range(len(words)):
        lab = labels[i] if i < len(labels) else ""
        w   = words[i]
        if lab and _norm_label(lab) in _GRAM_LABELS:
            flush()
            cur_label = _norm_label(lab)
            cur_words = [w] if w else []
        else:
            if cur_label is None and not cur_words:
                cur_label = None
                cur_words = [w] if w else []
            else:
                cur_words.append(w)

    flush()

    p = soup.new_tag("p")
    parts = []
    for lab, txt in out_segments:
        if not txt:
            continue
        if lab:
            parts.append(f"[{lab}: {txt}]")
        else:
            parts.append(txt)
    p.string = " ".join(parts).strip()
    if not p.string:
        return None
    p["data-sentence-analysis"] = "true"
    return p

# --- Heuristikk: span-basert analyse -------------------------------------

def _looks_like_span_analysis(p: Tag) -> bool:
    if p.name != "p":
        return False
    labels = []
    for sp in p.find_all("span"):
        cls = set(sp.get("class", []))
        if "gram-label" in cls or sp.get("data-label"):
            lab = _norm_label(sp.get("data-label") or sp.get_text(" ", strip=True))
            if lab in _GRAM_LABELS:
                labels.append(lab)
    return len(labels) >= 2

def _span_to_bracketed_p(par: Tag, soup) -> Tag | None:
    parts = []
    cur_label: str | None = None
    buffer: list[str] = []

    def flush():
        nonlocal cur_label, buffer
        txt = " ".join(t for t in buffer if t).strip()
        if txt:
            if cur_label:
                parts.append(f"[{cur_label}: {txt}]")
            else:
                parts.append(txt)
        cur_label, buffer = None, []

    for node in par.contents:
        if isinstance(node, Tag) and node.name == "span" and (
            "gram-label" in set(node.get("class", [])) or node.get("data-label")
        ):
            lab = _norm_label(node.get("data-label") or node.get_text(" ", strip=True))
            if lab in _GRAM_LABELS:
                flush()
                cur_label = lab
                continue
        if isinstance(node, NavigableString):
            buffer.append(str(node))
        elif isinstance(node, Tag):
            buffer.append(node.get_text(" ", strip=True))

    flush()
    newp = soup.new_tag("p")
    newp.string = " ".join(parts).strip()
    if newp.string:
        newp["data-sentence-analysis"] = "true"
        return newp
    return None

# --- Hjelpere for § 2.13.2 -----------------------------------------------------

def _doc_lang_local(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _normalize_token(s: str) -> str:
    s = (s or "").strip()
    # dropp kolon/parenteser/punktum som ofte følger etiketter
    s = s.strip(":()[]{}.")
    # bruk NFKD for å senke diakritika, men behold aksenter i spansk/fransk når vi sammenligner i settet:
    # vi beholder original og en "av-aksentert" kopi for fallback-match.
    return s

def _strip_accents(s: str) -> str:
    return "".join(c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c))

def _cell_text(el: Tag) -> str:
    return " ".join(el.stripped_strings)

def _first_data_row(table: Tag) -> Tag | None:
    # hvis thead finnes, bruk første rad i tbody; ellers første <tr> etter en ev. header-rad
    tbody = table.find("tbody", recursive=False)
    if tbody:
        tr = tbody.find("tr", recursive=False)
        return tr
    return table.find("tr", recursive=False)

def _iter_rows(table: Tag):
    tbody = table.find("tbody", recursive=False)
    rows = (tbody.find_all("tr", recursive=False) if tbody else table.find_all("tr", recursive=False))
    for tr in rows:
        yield tr

def _looks_like_conjugation_table(table: Tag) -> bool:
    # krav: minst 3 rader (overskrift kan mangle), og minst 2 kolonner
    rows = list(_iter_rows(table))
    if len(rows) < 3:
        return False
    # se på første-celle i hver rad: er flertallet pronomen?
    first_col = []
    for tr in rows:
        cells = tr.find_all(["th","td"], recursive=False)
        if len(cells) < 2:
            continue
        first = _cell_text(cells[0]).strip().lower()
        # fjern trailing kolon, parenteser
        first = _normalize_token(first).lower()
        first_col.append(first)
    if len(first_col) < 3:
        return False

    # score: antall som matcher i pron-mengdene (med/uten diakritika)
    hits = 0
    for tok in first_col:
        if not tok:
            continue
        if tok in _ALL_PRONS or _strip_accents(tok) in _ALL_PRONS:
            hits += 1

    # konservativ terskel: minst 50% av radene
    return hits >= max(2, len(first_col) // 2)

def _headers_for_columns(table: Tag) -> list[str]:
    # hent kolonneoverskrifter fra thead eller første rad hvis den er <th>-dominert
    headers: list[str] = []
    thead = table.find("thead", recursive=False)
    if thead:
        hrow = thead.find("tr", recursive=False)
        if hrow:
            cells = hrow.find_all(["th","td"], recursive=False)
            headers = [_cell_text(c) for c in cells]
    else:
        first_tr = table.find("tr", recursive=False)
        if first_tr:
            cells = first_tr.find_all(["th","td"], recursive=False)
            # tell th-andel
            if cells and sum(1 for c in cells if c.name == "th") >= max(1, len(cells)//2):
                headers = [_cell_text(c) for c in cells]
    return [h.strip() for h in headers]

def _extract_caption(table: Tag) -> str | None:
    cap = table.find("caption")
    if cap:
        return cap.get_text(" ", strip=True)
    title = table.get("title")
    if title:
        return str(title).strip()
    return None

def _make_title_p(soup, text: str) -> Tag:
    p = soup.new_tag("p")
    strong = soup.new_tag("strong")
    strong.string = text
    p.append(strong)
    return p

def _convert_conjugation_table(table: Tag, soup, logger) -> bool:
    if table.get("data-conjugation-converted") == "true":
        return False

    if not _looks_like_conjugation_table(table):
        return False

    rows = list(_iter_rows(table))
    if not rows:
        return False

    # Hvis første rad ser ut til å være header, dropp den fra data
    col_headers = _headers_for_columns(table)
    data_rows = rows[:]
    if col_headers and len(rows) > 1:
        # anta at første rad er header, fjern den
        data_rows = rows[1:]

    # bygg container
    wrapper = soup.new_tag("div")
    wrapper["class"] = ["conjugation"]
    wrapper["data-conjugation-converted"] = "true"

    # caption/overskrift (valgfritt)
    cap = _extract_caption(table)
    if cap:
        wrapper.append(_make_title_p(soup, cap))

    # tell antall kolonner i data (min med radene)
    max_cols = 0
    for tr in data_rows:
        cells = tr.find_all(["th","td"], recursive=False)
        max_cols = max(max_cols, len(cells))

    if max_cols < 2:
        return False  # ikke sikkert en konjugasjon

    # kolonne-navn utover 1. kolonne
    names_for_cols: list[str] = []
    if col_headers and len(col_headers) >= 2:
        names_for_cols = col_headers[1:]
    else:
        # prøv å hente fra vertikale header-celler i første kolonne? (vanskelig) → generiske navn
        for j in range(2, max_cols+1):
            names_for_cols.append(f"Form {j-1}")

    # 2 kolonner → én liste
    if max_cols == 2:
        ul = soup.new_tag("ul")
        ul["class"] = ["list-unstyled", "conjugation-list"]
        for tr in data_rows:
            cells = tr.find_all(["th","td"], recursive=False)
            if len(cells) < 2:
                continue
            person = _cell_text(cells[0]).strip()
            form   = _cell_text(cells[1]).strip()
            if not (person or form):
                continue
            li = soup.new_tag("li")
            # Person: form
            span_p = soup.new_tag("span"); span_p["class"] = ["person"]; span_p.string = person
            span_c = soup.new_tag("span"); span_c["class"] = ["form"]
            if form:
                span_c.string = f": {form}"
            else:
                span_c.string = ":"
            li.append(span_p); li.append(span_c)
            ul.append(li)
        wrapper.append(ul)

    else:
        # ≥3 kolonner → én liste per kolonne 2..N
        for col_idx in range(1, max_cols):
            # overskrift for denne formen
            heading = names_for_cols[col_idx-1] if col_idx-1 < len(names_for_cols) else f"Form {col_idx}"
            wrapper.append(_make_title_p(soup, heading))
            ul = soup.new_tag("ul")
            ul["class"] = ["list-unstyled", "conjugation-list"]
            for tr in data_rows:
                cells = tr.find_all(["th","td"], recursive=False)
                if len(cells) <= col_idx:
                    continue
                person = _cell_text(cells[0]).strip()
                form   = _cell_text(cells[col_idx]).strip()
                if not (person or form):
                    continue
                li = soup.new_tag("li")
                span_p = soup.new_tag("span"); span_p["class"] = ["person"]; span_p.string = person
                span_c = soup.new_tag("span"); span_c["class"] = ["form"]
                if form:
                    span_c.string = f": {form}"
                else:
                    span_c.string = ":"
                li.append(span_p); li.append(span_c)
                ul.append(li)
            wrapper.append(ul)

    # sett inn før tabellen og fjern den
    table.insert_before(wrapper)
    table.decompose()
    logger.debug("2.13.2 - Converted a conjugation table to list(s).")
    return True

# --- Hjelpere for § 2.14 -----------------------------------------------------


def _txt(n): return "".join(n.stripped_strings)

def _tokenize(val: str) -> set[str]:
    return set((val or "").lower().replace(";", " ").replace(",", " ").split())

def _is_poem_explicit(tag: Tag) -> bool:
    if getattr(tag, "name", None) is None:
        return False
    if tag.name == "section":
        cls = _tokenize(" ".join(tag.get("class", [])))
        if "poem" in cls: return True
        et = _tokenize(tag.get("epub:type", ""))
        if "poem" in et or "z3998:poem" in et: return True
    # Enkel støtte for <div class="poem"> som container
    if tag.name in {"div","article"}:
        cls = _tokenize(" ".join(tag.get("class", [])))
        et = _tokenize(tag.get("epub:type", ""))
        if ("poem" in cls) or ("poem" in et) or ("z3998:poem" in et):
            return True
    return False

def _already_normalized(sec: Tag) -> bool:
    if getattr(sec, "name", None) != "section":
        return False
    cls = _tokenize(" ".join(sec.get("class", [])))
    if "poem" not in cls:
        return False
    return bool(sec.find("div", class_="linegroup", recursive=False))

def _find_heading_in_or_before(container: Tag) -> Tag | None:
    # 1) direkte barn
    for h in container.find_all(_H_RX, recursive=False):
        return h
    # 2) nærmeste forrige søsken
    sib = container.previous_sibling
    while sib is not None:
        if isinstance(sib, Tag) and _H_RX.match(sib.name or ""):
            return sib
        sib = sib.previous_sibling
    return None

def _ensure_section_poem(container: Tag, soup) -> Tag:
    if container.name == "section":
        cls = set(container.get("class", []) or [])
        cls.add("poem")
        container["class"] = list(cls)
        return container
    sec = soup.new_tag("section")
    sec["class"] = ["poem"]
    container.insert_before(sec)
    sec.append(container.extract())
    return sec

def _split_p_on_br(p: Tag) -> list[list]:
    """Returner linjer som lister av noder; splitter på <br>."""
    lines, buf = [], []
    for child in list(p.children):
        if isinstance(child, Tag) and child.name == "br":
            lines.append(buf); buf = []
            child.extract()
        else:
            buf.append(child.extract())
    lines.append(buf)
    # fjern helt tomme linjer
    return [ln for ln in lines if any((isinstance(x, Tag) or (isinstance(x, NavigableString) and x.strip())))]

def _append_linegroup(sec: Tag, soup, stanzas: list[list[list]]):
    for stanza in stanzas:
        lg = soup.new_tag("div"); lg["class"] = ["linegroup"]
        for nodes in stanza:
            pl = soup.new_tag("p"); pl["class"] = ["line"]
            for n in nodes: pl.append(n)
            # trim ytterkanter
            if pl.contents and isinstance(pl.contents[0], NavigableString):
                pl.contents[0].replace_with(NavigableString(str(pl.contents[0]).lstrip()))
            if pl.contents and isinstance(pl.contents[-1], NavigableString):
                pl.contents[-1].replace_with(NavigableString(str(pl.contents[-1]).rstrip()))
            lg.append(pl)
        sec.append(lg)

def _guess_stanzas_from_lines(lines: list[list]) -> list[list[list]]:
    """Del på blanke linjer; hvis ingen blanke → én strofe."""
    stanzas, cur = [], []
    for ln in lines:
        if len(ln) == 1 and isinstance(ln[0], NavigableString) and not ln[0].strip():
            if cur: stanzas.append(cur); cur = []
        else:
            cur.append(ln)
    if cur: stanzas.append(cur)
    return stanzas or [lines]

def _extract_author_candidate(container: Tag) -> Tag | None:
    # Eksplisitt
    p = container.find("p", attrs={"epub:type": re.compile(r"(^| )z3998:author( |$)", re.I)}, recursive=False)
    if p: return p
    # Klassehint
    for cand in container.find_all("p", recursive=False):
        cls = _tokenize(" ".join(cand.get("class", [])))
        if {"author","forfatter","poet"} & cls:
            return cand
    # Kort siste-linje, ofte navn
    ps = container.find_all("p", recursive=False)
    if ps:
        tail = ps[-1]
        t = _txt(tail)
        if 2 <= len(t.split()) <= 7:
            return tail
    return None

def _place_author_after_linegroups(sec: Tag, author_p: Tag):
    author_p["epub:type"] = "z3998:author"
    author_p.extract()
    # finn siste linegroup
    last_lg = None
    for lg in sec.find_all("div", class_="linegroup", recursive=False):
        last_lg = lg
    if last_lg is not None:
        last_lg.insert_after(author_p)
    else:
        sec.append(author_p)

def _ensure_ids(sec: Tag, heading: Tag | None, soup):
    if heading and not heading.get("id"):
        base = "poem-title"; i = 1; hid = base
        while soup.find(id=hid): i += 1; hid = f"{base}-{i}"
        heading["id"] = hid
    if heading and heading.get("id"):
        sec["aria-labelledby"] = heading["id"]
    if not sec.get("id"):
        i = 1
        while soup.find(id=f"poem-{i}"): i += 1
        sec["id"] = f"poem-{i}"

def _normalize_poem_container(container: Tag, soup, *, logger) -> bool:
    if _already_normalized(container):
        return False

    # Finn og flytt heading (om nødvendig)
    heading = _find_heading_in_or_before(container)
    sec = _ensure_section_poem(container, soup)

    if heading and heading.parent is not sec:
        sec.insert(0, heading.extract())

    # Lag linjer/linegroup(s)
    ps = sec.find_all("p", recursive=False)
    has_line = any("line" in (p.get("class", []) or []) for p in ps)
    if has_line:
        # bare pakk eksisterende p.line i linegroup om ikke finnes
        if not sec.find("div", class_="linegroup", recursive=False):
            lg = soup.new_tag("div"); lg["class"] = ["linegroup"]
            for p in [p for p in ps if "line" in (p.get("class", []) or [])]:
                lg.append(p.extract())
            sec.append(lg)
    else:
        lines = []
        for p in list(ps):
            brs = p.find_all("br")
            if brs:
                parts = _split_p_on_br(p)
                lines.extend(parts if parts else [[NavigableString(_txt(p))]])
                p.decompose()
            else:
                # Heuristikk: kort <p> → linje; ellers beholde som én linje likevel
                nodes = [n.extract() for n in list(p.contents)]
                lines.append(nodes if nodes else [NavigableString("")])
                p.decompose()
        stanzas = _guess_stanzas_from_lines(lines)
        _append_linegroup(sec, soup, stanzas)

    # Forfatterplassering
    author = _extract_author_candidate(sec)
    if author:
        _place_author_after_linegroups(sec, author)

    _ensure_ids(sec, heading, soup)
    return True

# --- Hjelpere for § 2.15 -----------------------------------------------------


def _doc_lang(soup) -> str:
    html = getattr(soup, "html", None)
    if not html:
        return "no"
    return (html.get("xml:lang") or html.get("lang") or "no").lower()

def _closest_lang(node: Tag | NavigableString, default: str) -> str:
    p = node if isinstance(node, Tag) else node.parent
    while p is not None:
        if isinstance(p, Tag):
            v = (p.get("xml:lang") or p.get("lang"))
            if v:
                return v.lower()
        p = getattr(p, "parent", None)
    return default.lower()

def _should_skip_textnode(text_node: NavigableString) -> bool:
    if not text_node or not str(text_node).strip():
        return True
    anc = text_node.parent
    while anc is not None:
        if isinstance(anc, Tag) and anc.name in _SKIP_TAGS:
            return True
        anc = getattr(anc, "parent", None)
    return False

def _parent_has_lang(text_node: NavigableString) -> bool:
    p = text_node.parent
    if not isinstance(p, Tag):
        return False
    return p.has_attr("xml:lang") or p.has_attr("lang")

def _find_script_runs(text: str):
    """Returner ikke-latinske skriptkjerner som (start, end, lang), ikke overlappende."""
    runs = []
    i, n = 0, len(text)
    while i < n:
        ch = text[i]
        matched = None
        rx_use = None
        for lang, rx in _SCRIPT_LANGS:
            if rx.match(ch):
                matched, rx_use = lang, rx
                break
        if matched:
            j = i + 1
            while j < n and rx_use.match(text[j]):
                j += 1
            runs.append((i, j, matched))
            i = j
        else:
            i += 1
    # slå sammen nabokjøringer av samme lang
    merged = []
    for st, en, lg in runs:
        if merged and merged[-1][2] == lg and st == merged[-1][1]:
            merged[-1] = (merged[-1][0], en, lg)
        else:
            merged.append((st, en, lg))
    return merged

def _find_latin_englishish_runs(text: str, min_len=12):
    """Konservativ flagging av latinsk-tekst som sannsynligvis er engelsk."""
    candidates = []
    for m in re.finditer(r"([A-Za-z\u00C0-\u024F][A-Za-z\u00C0-\u024F'\- ]{"+str(min_len)+r",})", text):
        seg = m.group(0)
        toks = re.findall(r"[A-Za-z']+", seg.lower())
        if sum(1 for t in toks if t in _EN_STOP) >= 3:
            candidates.append((m.start(), m.end()))
    return candidates

def _apply_runs_replace(soup, text_node: NavigableString, actions):
    """
    Bytt *hele* tekstnoden i én operasjon:
      actions = liste av dicts med:
        {"start": int, "end": int, "kind": "wrap", "lang": "xx"} eller
        {"start": int, "end": int, "kind": "flag", "base": "no"}
    Forutsetter ikke-overlappende, sortert stigende på start.
    """
    if not isinstance(text_node, NavigableString):
        return False
    parent = text_node.parent
    if not isinstance(parent, Tag):
        return False

    s = str(text_node)
    if not s:
        return False

    actions = sorted(actions, key=lambda a: a["start"])
    new_nodes = []
    pos = 0

    for a in actions:
        st, en = a["start"], a["end"]
        if st > pos:
            chunk = s[pos:st]
            if chunk:
                new_nodes.append(NavigableString(chunk))

        mid = s[st:en]
        if not mid:
            continue

        if a["kind"] == "wrap":
            span = soup.new_tag("span")
            span["xml:lang"] = a["lang"]
            span.append(NavigableString(mid))
            new_nodes.append(span)
        else:  # flag
            span = soup.new_tag("span")
            span["data-llm-pending"] = "lang-inline"
            span["data-base-lang"] = a.get("base") or ""
            sample = mid.strip()
            if len(sample) > 160:
                sample = sample[:157] + "…"
            span["data-sample"] = sample
            span.append(NavigableString(mid))
            new_nodes.append(span)

        pos = en

    if pos < len(s):
        tail = s[pos:]
        if tail:
            new_nodes.append(NavigableString(tail))

    # Erstatt i parent (én gang)
    try:
        text_node.replace_with(new_nodes[0])
    except Exception:
        return False

    cur = new_nodes[0]
    for nn in new_nodes[1:]:
        cur.insert_after(nn)
        cur = nn

    return True

# =============== APPLY REQUIREMENTS ================

def apply_requirements(args, logger, soup, folders, comic_text_rpc=None):
    logger.info('Applying Statped Mark-up Requirements')

    use_llm = False #args.llm
    aggressive = False #args.aggressive

    print(f'type args in apply_requirements: {type(args)}')
    print(f'type logger in apply_requirements: {type(logger)}')

    '''
    try:
        args.grade = int(args.grade)
    except:
        args.grade = 10
    '''

    if args.grade:
        args.grade = int(args.grade)
    else:
        for keyword in soup('meta', attrs={'name':'dc:subject.keyword'}):
            if 'content' in keyword.attrs and keyword['content'].isdigit():
                args.grade = int(keyword['content'])
                break
    if not args.grade:
        args.grade = 10  # default høyeste nivå

    logger.info(f'Assumed grade level: {args.grade}')

    # Fix soup.html['lang'] if needed
    if 'lang' not in soup.html.attrs.keys():
        if 'xml:lang' in soup.html.attrs.keys():
            soup.html['lang'] = soup.html['xml:lang']
            logger.warning(f'html tag missing lang attribute, using xml:lang="{soup.html["lang"]}"')
        else:
            soup.html['lang'] = 'no'
            logger.warning('html tag missing lang and xml:lang attributes, assuming lang="no"')


    # 2.1.1 CSS — ensure exact Statped requirement
    logger.info('2.1.1 - Ensuring ebok.css link in <head>')

    head = soup.head
    if head is None:
        head = soup.new_tag('head')
        # sørg for at head havner tidlig i dokumentet
        if soup.html:
            soup.html.insert(0, head)
        else:
            soup.insert(0, head)

    CSS_HREF = 'ebok.css'  # Statped 2.1.1: uten 'css/'-mappe
    css_basename = 'ebok.css'

    # Finn eksisterende stylesheet-lenker
    links = head.find_all('link', attrs={'rel': lambda v: v and 'stylesheet' in v.lower()})
    has_ebok = None
    for link in links:
        href = (link.get('href') or '').strip()
        if href.lower().split('/')[-1] == css_basename:
            has_ebok = link
            break

    # Fjern andre stylesheets for å unngå konflikter
    removed = 0
    for link in list(links):
        href = (link.get('href') or '').strip()
        if href.lower().split('/')[-1] != css_basename:
            link.decompose()
            removed += 1
    if removed:
        logger.warning(f'2.1.1 - Removed {removed} other stylesheet link(s)')

    # Sett inn eller normaliser ebok.css-lenken
    if has_ebok is None:
        link = soup.new_tag('link', rel='stylesheet', type='text/css', href=CSS_HREF)
        # legg den før ev. <style> for å gi lokal <style> mulighet til å overstyre, om ønsket
        first_style = head.find('style')
        if first_style:
            first_style.insert_before(link)
        else:
            head.append(link)
        logger.info('2.1.1 - Inserted <link rel="stylesheet" href="ebok.css" />')
    else:
        has_ebok['href'] = CSS_HREF
        has_ebok['type'] = 'text/css'
        logger.info('2.1.1 - Normalized existing ebok.css link')

    # Plasser selve CSS-filen ved siden av ut-XHTML (matching href)
    copy_target_dir = folders['output']  # ingen 'css/'-undermappe iht. §2.1.1
    Path(copy_target_dir).mkdir(parents=True, exist_ok=True)
    copyfile(path.join(folders['static'], 'ebok.css'),
            path.join(copy_target_dir, 'ebok.css'))

    # 2.6.1  - Boxes in mathematics books
    # Moved here, before 2.6 and before 2.1.2 relocation
    """
    2.6.1 Boxes in mathematics books
    - I mattebøker konverteres reelle <aside>-bokser til <div> (del av hovedtekst).
    - Hopper over prodnote/fig-desc/glossary/dl.
    - Normaliserer ramme-klasser; justerer evt. headingnivå.
    - Idempotent; merker med data-original-tag for sporbarhet.
    - Tips: Kjør før 2.6 og før 2.1.2-relokering.
    """
    logger.info("2.6.1 - Boxes in mathematics books")

    if not getattr(args, "mathematics", False):
        logger.info("2.6.1 - Not a mathematics book; skipping.")
    else:
        llm = _ensure_llm_client(logger, use_llm) if use_llm else None

        converted = kept_aside = heading_adjusted = framed = 0

        for aside in list(soup.find_all("aside")):
            if _skip_math_aside(aside):
                kept_aside += 1
                continue

            # Valgfritt: la LLM si fra om denne spesifikt skal forbli aside (unntak fra hovedregelen)
            if use_llm and llm and getattr(llm, "available", False):
                prev_sib = aside.find_previous(lambda t: getattr(t, "name", None) in ("p","div","section"))
                next_sib = aside.find_next(lambda t: getattr(t, "name", None) in ("p","div","section"))
                resp = llm.classify_math_box_keep_aside(
                    html_snippet=str(aside)[:2000],
                    prev_snip=(prev_sib.get_text(" ", strip=True) if prev_sib else ""),
                    next_snip=(next_sib.get_text(" ", strip=True) if next_sib else ""),
                )
                if bool((resp or {}).get("keep_as_aside", False)):
                    kept_aside += 1
                    # men normaliser klasser hvis den likevel er aside:
                    _normalize_frame_classes(aside)
                    framed += 1
                    continue

            # Konverter til <div>, bevar alle attributter og innhold
            div = soup.new_tag("div")
            for k, v in list(aside.attrs.items()):
                div.attrs[k] = v
            # sporbarhet/idempotens
            div.attrs["data-original-tag"] = "aside"
            div.attrs["data-math-box"] = "true"

            for n in list(aside.contents):
                div.append(n.extract())
            aside.replace_with(div)
            converted += 1

            # Headingnivå inne i boksen (nå som <div> i hovedløpet) – valgfritt men nyttig
            h = div.find(_HEADING_RX)
            if h:
                target = f"h{_nearest_heading_level(div)}"
                if h.name != target:
                    h.name = target
                    heading_adjusted += 1

            # Sørg for ramme-klasse
            _normalize_frame_classes(div)
            framed += 1

        logger.info(
            "2.6.1 - Done. converted=%d, kept_aside=%d, headings_adjusted=%d, framed=%d",
            converted, kept_aside, heading_adjusted, framed
        )

    # 2.1.2 Relocation of elements
    # TODO: This specification is unclear

    """
    Implementerer §2.1.2 Relocation of elements.

    - Rekkefølge: 1) figures/images, 2) asides, 3) glossaries/description lists.
    - Alle flyttede elementer skal plasseres *før* oppgave-delen (om den finnes).
    - Hvis LLM er på: spør modellen om et <aside> er 'integrert' i hovedteksten.
      Integrerte asides blir *ikke* flyttet; de konverteres til <div> og beholdes der de står.
    """
    if args.relocate:
        logger.info("2.1.2 - Relocation disabled (--no-relocate).")

        llm = _ensure_llm_client(logger, args.llm)

        moved_counts_total = {"images": 0, "asides": 0, "glossaries": 0, "asides_kept_as_div": 0}
        chapter_containers = _iter_chapter_like_containers(soup)

        for container in chapter_containers:
            # Samle kandidater i dokumentrekkefølge (bare *én gang* pr. node)
            images, asides, glossaries = [], [], []
            seen = set()

            # Vi prioriterer *toppnivå* elementer i kapittel/container (det er her “flyt” brytes)
            for child in list(container.children):
                if not getattr(child, "name", None):
                    continue
                key = id(child)
                if key in seen:
                    continue

                name = child.name.lower()

                def _has_taskish_descendant(el):
                    # 2.1.2
                    return el.find(lambda t: getattr(t, "name", None) and _is_task_container(t)) is not None

                if (args.llm and llm and not (_is_task_container(child) or 
                    _has_taskish_descendant(child))):
                    txt = (child.get_text(" ", strip=True) or "").lower()
                    if any(token in txt for token in ("oppgave", "oppgåve", "task", "exercise")):
                        # spør LLM om figuren er "integral" for oppgaven
                        resp = llm.classify_task_bound_figure(
                            html_snippet=str(child)[:2000],
                            context_before=_get_text_snippet(child.find_previous("p") or child),
                            context_after=_get_text_snippet(child.find_next("p") or child),
                        )
                        if resp.get("task_bound", False):
                            # ikke flytt
                            pass
                        else:
                            images.append(child); seen.add(key)
                    else:
                        images.append(child); seen.add(key)

                # 1) FIGURES/IMAGES
                if name in ("figure",):
                    # hopp over hvis figuren hører til oppgave
                    if _in_task_or_key_ancestor(child) or _is_task_container(child):
                        pass  # ikke flytt
                    else:
                        images.append(child); seen.add(key)
                    continue
                if name not in ("figure",) and child.find("img") and name not in ("header", "footer", "nav"):
                    # Enkel heuristikk: enslige bilder blokkvis
                    # Unngå å ta med headings etc. som bare *inneholder* img-ikoner
                    if child.name.lower() in ("p", "div", "section", "aside"):
                        # P med mye tekst + et lite ikon = ikke flytt; men korte "bildetekstblokker" flyttes
                        txt_len = len(_get_text_snippet(child))
                        if child.name == "p" and txt_len > 120:
                            pass  # sannsynligvis inline-ikon, ikke flytt
                        else:
                            images.append(child); seen.add(key); continue

                # 2) ASIDES
                if name == "aside":
                    # Hvis aside inneholder <dl>, behandle som glossary (kategori 3)
                    if _is_glossary_container(child):
                        glossaries.append(child); seen.add(key); continue

                    # LLM-vurdering av "integrert?"
                    integral = False
                    if args.llm and llm.available:
                        prev_sib = child.find_previous(lambda t: getattr(t, "name", None) in ("p","div","section"))
                        next_sib = child.find_next(lambda t: getattr(t, "name", None) in ("p","div","section"))
                        resp = llm.classify_aside_integral(
                            html_snippet=str(child)[:2000],
                            prev_snip=_get_text_snippet(prev_sib) if prev_sib else "",
                            next_snip=_get_text_snippet(next_sib) if next_sib else "",
                        )
                        integral = bool(resp.get("integral", False))

                    if integral:
                        # Ikke flytt. Konverter til <div> (bevar attrs) slik standarden krever for integrert stoff.
                        div = soup.new_tag("div")
                        # kopier attributter
                        for k, v in list(child.attrs.items()):
                            div.attrs[k] = v
                        # markér opprinnelse for revisjon
                        div.attrs["data-original-tag"] = "aside"
                        div.attrs["data-integral"] = "true"
                        # flytt innhold
                        for n in list(child.contents):
                            div.append(n.extract())
                        child.replace_with(div)
                        moved_counts_total["asides_kept_as_div"] += 1
                    else:
                        asides.append(child); seen.add(key); continue

                # 3) GLOSSARY/DESCRIPTION LISTS (uansett om de var i aside eller ikke)
                if name == "dl" or _is_glossary_container(child):
                    glossaries.append(child); seen.add(key); continue

            anchor = None
            # Find anchor
            for el in container.descendants:
                if getattr(el, "name", None) and _is_task_heading(el):
                    anchor = el
                    break

            if anchor:
                top = anchor
                while top.parent is not None and top.parent is not container:
                    top = top.parent
                anchor_top = top
            else:
                anchor_top = None

            # Flytt i prioritert rekkefølge
            def _insert_before_anchor_or_end(node):
                if anchor_top is not None:
                    try:
                        anchor_top.insert_before(node)
                    except Exception:
                        container.append(node) # TODO: check
                else:
                    container.append(node)

            for node in images:
                _tag_moved_origin(node)
                node.extract()
                _insert_before_anchor_or_end(node)
                moved_counts_total["images"] += 1

            for node in asides:
                _tag_moved_origin(node)
                node.extract()
                _insert_before_anchor_or_end(node)
                moved_counts_total["asides"] += 1

            for node in glossaries:
                _tag_moved_origin(node)
                node.extract()
                _insert_before_anchor_or_end(node)
                moved_counts_total["glossaries"] += 1

        logger.info(
            "2.1.2 - Relocated: images=%d, asides=%d, glossaries=%d; kept_as_div=%d",
            moved_counts_total["images"],
            moved_counts_total["asides"],
            moved_counts_total["glossaries"],
            moved_counts_total["asides_kept_as_div"],
        )

    # 2.1.3 Uppercase text
    # Ensure commit
    """
    2.1.3 Uppercase text (HEADINGS):
    - Ikke bruk uppercase headings; bruk initial stor bokstav og ellers små bokstaver.
    - Ikke Title Case 'hver Ord'.
    - Unntak: akronymer/initialismer, romertall; bevar matte/kode.
    - Valgfritt LLM (args.llm): kan returnere tokens (egennavn/brand) som skal bevares.
    """
    logger.info("2.1.3 - Uppercase text ")

    for node in soup(string=True):
        if node.parent.name in ['script', 'style', 'math'] or "math" in node.get("class", []) or isinstance(node, NavigableString) == False:
            continue

        if node.isupper() and len(node) > 2:
            node.replace_with(node[0] + node[1:].lower())
        else:
            original_text = str(node)
            '''
            Hva denne gjør:
            [A-ZÆØÅ]{2,}: Ser kun på ord med 2 eller flere bokstaver (ignorerer "I" og "Å").
            Sjekken if ...:
            not original_text[:m.start()].strip(): Sjekker om ordet er først i noden.
            original_text[:m.start()].strip().endswith('.'): Sjekker om forrige tegn (minus mellomrom) er et punktum.
            Resultatet:
            Hvis en av sjekkene stemmer: Beholder første bokstav stor, resten små (f.eks. Meir, Ntnu).
            Ellers: Hele ordet blir små bokstaver (f.eks. ntnu, lese).
            Eksempel:
            "MEIR Å LESE. NTNU ER BRA" → "Meir Å lese. Ntnu er bra"
            "Sjekk NTNU" → "Sjekk ntnu"
            '''
            new_text = re.sub(r'\b[A-ZÆØÅ]{2,}\b',
                lambda m: (m.group(0)[0] + m.group(0)[1:].lower())
                if not original_text[:m.start()].strip() or original_text[:m.start()].strip().endswith('.')
                else m.group(0).lower(),
                original_text)


            if new_text != original_text and node.parent:
                node.replace_with(new_text)


    # 2.1.5 Blank pages where elements have been moved
    # NOTE: 2.1.5 must be done before 2.1.4, because it relies on data-moved-from-seg tags
    """
    2.1.5: Når elementer er flyttet bort og siden står tom:
    sett inn nynorsk/bokmål-frasen foran den neste pagebreaken i segmentet.
    """
    logger.info("2.1.5 - Blank pages where elements have been moved")

    pbs = _iter_pagebreaks_in_order(soup)

    if not len(pbs) < 2:
        # Samle hvor det *kom fra* noe (merkingen lagt på i §2.1.2)
        moved_from_counts = Counter()
        for moved in soup.find_all(attrs={"data-moved-from-seg": True}):
            seg = moved.get("data-moved-from-seg")
            if seg:
                moved_from_counts[seg] += 1

        if not moved_from_counts:
            logger.info("2.1.5 - No moved elements tagged; nothing to do.")

        # Valgfri LLM — normalt ikke nødvendig
        llm = _ensure_llm_client(logger, args.llm) if args.llm else None

        inserted = 0
        for i in range(1, len(pbs)):
            prev, curr = pbs[i-1], pbs[i]
            seg_id = curr.get("id")
            if not seg_id:
                continue

            # Bare vurder segmenter som faktisk hadde noe flyttet ut
            if moved_from_counts.get(seg_id, 0) == 0:
                continue

            between = _collect_between(prev, curr)
            has_visible, ambiguous = _has_visible_content(between)
            if has_visible:
                continue

            # Idempotens og 'riktig' tekst: hvis "Blank side." allerede står der, erstatt med flyttet-frasen
            prev_sig = _find_prev_significant(curr)
            prev_is_p = getattr(prev_sig, "name", "") == "p"
            prev_text_lower = (prev_sig.get_text(strip=True).lower() if prev_is_p else "")

            nearest_language = ''
            cur = curr
            while cur is not None:
                for key in ("{http://www.w3.org/XML/1998/namespace}lang", "xml:lang", "lang"):
                    val = cur.attrs.get(key)
                    if val:
                        nearest_language = str(val).lower()
                        break
                cur = getattr(cur, "parent", None)

            if nearest_language.startswith("nn"):
                phrase = "Innhaldet på denne sida har blitt flytta."
            else:
                phrase = "Innholdet på denne siden har blitt flyttet."

            if prev_text_lower in _BLANK_MARKERS:
                if prev_text_lower != phrase.lower():
                    # erstatt "Blank side." (eller feil variant) med riktig flyttet-frase
                    prev_sig.string.replace_with(phrase)
                    logger.info(f'2.1.5 - Replaced existing marker with "{phrase}" before {seg_id}')
                continue

            # (Svært) ambig: la ev. LLM si nei (typisk ikke nødvendig)
            if args.llm and ambiguous:
                try:
                    resp = llm._rpc({
                        "action": "is_moved_blank_page",
                        "between_text": ambiguous,
                        "had_moved_out": True
                    })
                    if not bool(resp.get("blank", True)):
                        continue
                except Exception as e:
                    logger.warning(f"2.1.5 - LLM unavailable ({e}); continuing with deterministic rule.")

            # Sett inn frasen på blokknivå før 'curr'
            p = soup.new_tag("p")
            p.string = phrase
            anchor = _find_block_insertion_anchor(curr)
            anchor.insert_before(p)
            inserted += 1

            pid = prev.get("id") or "?"
            cid = seg_id
            logger.info(f'2.1.5 - Inserted "{phrase}" between pagebreaks {pid} -> {cid}')

        logger.info(f"2.1.5 - Done. Inserted {inserted} moved-blank markers.")

    # 2.1.4 Blank pages in the original source
    """
    2.1.4 Blank pages in the original source
    Sett inn <p>Blank side.</p> mellom to påfølgende pagebreaks der det ikke finnes
    synlig innhold imellom.
    """
    logger.info("2.1.4 - Blank pages in the original source")
    pbs = _iter_pagebreaks_in_order(soup)
    if not len(pbs) < 2:
        # Valgfritt: LLM (normalt ikke nødvendig)
        llm = _ensure_llm_client(logger, args.llm) if args.llm else None

        inserted = 0
        for i in range(1, len(pbs)):
            prev, curr = pbs[i-1], pbs[i]
            between = _collect_between(prev, curr)
            has_visible, ambiguous = _has_visible_content(between)
            if has_visible:
                continue

            # Idempotens: sjekk om "Blank side." allerede står rett før curr (signifikant node)
            prev_sig = _find_prev_significant(curr)
            if (getattr(prev_sig, "name", "") == "p" and
                (prev_sig.get_text(strip=True) or "").lower() == "blank side."):
                continue

            # LLM kun for ekstremt ambigue mini-fragmenter (f.eks. '—' alene)
            if args.llm and ambiguous:
                try:
                    resp = llm._rpc({
                        "action": "is_effectively_blank_page",
                        "between_text": ambiguous
                    })
                    if not bool(resp.get("blank", True)):
                        continue  # LLM mener ikke blank, hopp over
                except Exception as e:
                    logger.warning(f"2.1.4 - LLM unavailable ({e}); continuing with deterministic rule.")

            # Sett inn "Blank side." før curr, på blokknivå
            p = soup.new_tag("p")
            p.string = "Blank side."

            anchor = _find_block_insertion_anchor(curr)
            anchor.insert_before(p)
            inserted += 1

            cid = curr.get("id") or "?"
            pid = prev.get("id") or "?"
            logger.info(f'2.1.4 - Inserted "Blank side." between pagebreaks {pid} -> {cid}')

        logger.info(f"2.1.4 - Done. Inserted {inserted} 'Blank side.' paragraphs.")


    # 2.1.6 Use of <em> and <strong>

    # 2.1.6.1 Do not use double emphasis
    """
    2.1.6.1: Fjern dobbel vektlegging:
    - Område under både <em> og <strong> skal ha KUN <strong>.
    - Rene <em>-områder skal bestå.
    - Idempotent.
    """
    logger.info("2.1.6.1 - Do not use double emphasis")

    changed = True
    total_changes = 0

    while changed:
        changed = False

        # 1) Enkel case: <strong> inne i <em> (på en eller annen dybde) -> splitt em rundt strong
        #    Start med innerste <strong> for stabil splitting
        for s in soup('strong'):
            # Har s en em-ancestor?
            if s.find_parent("em"):
                """
                strong er (potensielt dypt) inni en <em>.
                Vi løfter strong ut av nærmeste <em> slik at overlapp forsvinner:
                <em>[left] <... strong ...> [right]</em>  ->  <em>[left]</em><strong>...</strong><em>[right]</em>
                """
                em = strong.find_parent("em")
                if not em:
                    continue

                # Finn nærmeste direkte barn av em som bærer strong i seg
                carrier = strong
                while carrier.parent is not em:
                    carrier = carrier.parent

                # del em.contents i left / carrier / right
                left_nodes, right_nodes = [], []
                seen = False
                for node in list(em.contents):  # snapshot
                    if node is carrier:
                        seen = True
                        continue
                    if not seen:
                        left_nodes.append(node)
                    else:
                        right_nodes.append(node)

                # bygg <em> for venstre og høyre deler (kun hvis ikke tomt)
                if left_nodes:
                    left_em = soup.new_tag("em")
                    for n in left_nodes:
                        left_em.append(n.extract())
                    em.insert_before(left_em)

                # flytt carrier (som kan være et span/div/... med strong inni) ut
                em.insert_before(carrier.extract())

                if right_nodes:
                    right_em = soup.new_tag("em")
                    for n in right_nodes:
                        right_em.append(n.extract())
                    em.insert_before(right_em)

                # rydde opp: em blir nå tom -> fjern
                em.decompose()

                logger.info("2.1.6.1 - Split <em> around <strong> to drop overlap")
                total_changes += 1
                changed = True

        # 2) Motsatt: <em> inne i <strong> (overlappet del skal være strong)
        #    Her er det trygt å fjerne <em> som er under en <strong>-ancestor
        for em in list(soup.find_all("em")):
            if em.find_parent("strong"):
                em.unwrap()
                logger.info("2.1.6.1 - Unwrapped <em> under <strong> (overlap -> strong only)")
                total_changes += 1
                changed = True

        # 3) Rydd opp trivielle ting (nestede like tagger, tomme)
        total_changes += _unwrap_nested_same_tags(soup, "em")
        total_changes += _unwrap_nested_same_tags(soup, "strong")
        removed = 0
        for nm in ("em", "strong"):
            for t in list(soup.find_all(nm)):
                # tom hvis ingen innhold eller kun whitespace
                if not t.contents or all(
                    isinstance(c, NavigableString) and not str(c).strip()
                    for c in t.contents
                ):
                    t.decompose()
                    removed += 1
        total_changes += removed 

    logger.info(f"2.1.6.1 - Finished. Changes applied: {total_changes}")

    # 2.1.6.2 Headings in <em> or <strong>
    """
    2.1.6.2: Ikke bruk <em>/<strong> i overskrifter (h1–h6).
    Fjerner kun <em>/<strong> tagger inne i headings, bevarer resten.
    Hopper over tilfeller inne i <code>/<pre>/<math>.
    Idempotent.
    """
    logger.info("2.1.6.2 - Headings in <em> or <strong>")
    changed = 0
    heads = soup(re.compile(r"^h[1-6]$", re.I))

    for h in heads:
        # Finn alle em/strong i headingen (dyp søk), men skipp hvis de ligger inne i code/pre/math
        targets = []
        for node in h(["em", "strong"]):
            if node.find_parent(_SKIP_INSIDE):
                # Ikke rør vektmerking inne i kode/matte
                continue
            targets.append(node)

        for node in targets:
            preview = (node.get_text(" ", strip=True) or "")[:60]
            node.unwrap()
            changed += 1
            if preview:
                logger.info(f'2.1.6.2 - Unwrapped emphasis in heading: "{preview}"')

    logger.info(f"2.1.6.2 - Done. Removed {changed} <em>/<strong> tag(s) inside headings.")

    # NOTE: 2.1.6.4 is placed before 2.1.6.3 because that yields a more stable processing order (full-paragraph emphasis is easier to detect and fix before we start splitting partial emphasis).

    # 2.1.6.4 Paragraphs in <em> or <strong>
    """
    2.1.6.4: Ikke bruk <em>/<strong> for *hele* avsnitt.
    Hvis *alt reelt innhold* i <p> ligger under em/strong, unwrap alle em/strong.
    Idempotent og forsiktig (rører ikke delvis uthevede avsnitt).
    """
    logger.info("2.1.6.4 - Paragraphs in <em> or <strong>")
    changed = 0

    def _has_em_or_strong_ancestor(node) -> bool:
        # 2.1.6.3
        p = getattr(node, "parent", None)
        while p is not None:
            if getattr(p, "name", "").lower() in ("em","strong"):
                return True
            p = getattr(p, "parent", None)
        return False

    for p in soup.find_all("p"):
        # Rask sjekk: finnes det i det hele tatt em/strong i avsnittet?
        if not p.find(["em","strong"]):
            continue

        # tekst-noder
        paragraph_fully_emphasized = True
        s = str(p)
        is_ignorable_text_node = True if not s or not s.strip() else bool(_PUNCT_ONLY_RX.match(s))
        for t in p.find_all(string=True):
            if is_ignorable_text_node:
                continue
            if not _has_em_or_strong_ancestor(t):
                paragraph_fully_emphasized = False

        # innholdstagger
        for el in p.find_all(_CONTENT_TAGS):
            # tomme 'sup/sub/abbr' uten tekst behandles via tekst-noder;
            # men for sikkerhets skyld krever vi at også disse ligger under em/strong
            if not _has_em_or_strong_ancestor(el):
                paragraph_fully_emphasized = False

        if not paragraph_fully_emphasized:
            continue

        # Unwrap alle em/strong under dette avsnittet
        for ems in list(p.find_all(["em","strong"])):
            ems.unwrap()
        changed += 1
        prev = (p.get_text(" ", strip=True) or "")[:60]
        logger.info(f'2.1.6.4 - Unwrapped full-paragraph emphasis: "{prev}"')

    logger.info(f"2.1.6.4 - Done. Paragraphs fixed: {changed}")

    # 2.1.6.3 Use of <em> or <strong> in words and expressions
    """
    2.1.6.3: Presis bruk av <em>/<strong> rundt ord/uttrykk.
    - Ikke inkluder ledende/etterfølgende mellomrom i taggen.
    - Ikke inkluder setningsslutt-tegn i taggen (med mindre hele setningen var ment å være vektlagt;
      enkel heuristikk: hvis taggen rommer flere setninger -> splitt i separate tagger).
    - Hvis én tag dekker flere setninger (ren tekst), splitt ved EoS.
    """
    logger.info("2.1.6.3 - Use of <em>/<strong> in words and expressions")

    def _split_multi_sentence_emphasis(soup, tag):
        """
        Hvis taggen har ren tekst og inneholder flere setninger,
        splitt til separate <tagname> ved EoS. Behold EoS-tegn utenfor.
        """
        if not all(not getattr(c, "name", None) for c in tag.contents):
            return False

        txt = tag.get_text()
        parts = SENT_SPLIT_RX.split(txt)  # [chunk, eos, space, chunk, eos, space, ...]
        if len(parts) == 1:
            return False  # ingen splitt

        made_change = False
        # Vi bygger en sekvens: <em>chunk</em> eos(space) <em>chunk</em> ...
        # Start med å erstatte original-tag med første <em>/<strong>
        name = tag.name
        parent = tag.parent

        def _make_tag(payload: str):
            t = soup.new_tag(name)
            t.append(NavigableString(payload))
            return t

        # Akkumulerer ny sekvens
        new_nodes = []
        i = 0
        # Første chunk
        if parts[i]:
            new_nodes.append(_make_tag(parts[i]))
        i += 1
        while i < len(parts):
            eos = parts[i] or ""
            space = parts[i+1] if i+1 < len(parts) else ""
            next_chunk = parts[i+2] if i+2 < len(parts) else ""
            # EoS tegn ut av em/strong:
            if eos:
                new_nodes.append(NavigableString(eos))
            if space:
                new_nodes.append(NavigableString(space))
            if next_chunk:
                new_nodes.append(_make_tag(next_chunk))
            i += 3

        # Erstatt original
        for n in new_nodes[::-1]:
            tag.insert_after(n)
        tag.decompose()
        made_change = True
        return made_change

    changed_total = 0
    # Prosesser både <em> og <strong>
    for tag in list(soup.find_all(["em", "strong"])):
        # 1) Trim whitespace inni taggen (flytt ut)
        changed = False
        # Move leading space out
        if (t := _leftmost_text_node(tag)) is not None:
            s = str(t)
            leading = len(s) - len(s.lstrip())
            if leading > 0:
                # flytt ut foran taggen
                ws = s[:leading]
                t.replace_with(s[leading:])
                tag.insert_before(ws)
                changed = True

        # Move trailing space out
        if (t := _rightmost_text_node(tag)) is not None:
            s = str(t)
            trailing = len(s) - len(s.rstrip())
            if trailing > 0:
                # flytt ut etter taggen
                ws = s[-trailing:]
                t.replace_with(s[:-trailing])
                tag.insert_after(ws)
                changed = True

        # 2) Hvis ren tekst og flere setninger -> splitt i separate tagger
        if (all(not getattr(c, "name", None) for c in tag.contents) and 
            SENT_SPLIT_RX.search(tag.get_text()) and
            _split_multi_sentence_emphasis(soup, tag)):
                logger.info("2.1.6.3 - Split multi-sentence emphasis into separate tags")
                changed_total += 1
                continue  # original tag er nå borte; neste loop

        # 3) Flytt setningsslutt-tegn ut av taggen
        move = False 
        """
        Flytt setningsslutttegn ut av taggen (hvis tilstede i siste tekstnode).
        Lar hermetegn/parantes som ligger ETTER punktum være med ut.
        """
        if (t := _rightmost_text_node(tag)) is not None:
            s = str(t)
            if (m := EOS_PUNCT_RX.search(s)):
                eos = m.group(1)         # . ! ? …
                closers = m.group(2)     # ) ” ’ ] …
                keep = s[:m.start()]
                if keep != s:
                    t.replace_with(keep)
                    # Sett eos + closers etter taggen (i korrekt rekkefølge)
                    tail = eos + closers
                    tag.insert_after(NavigableString(tail))
                    move = True
        if move:
            logger.info("2.1.6.3 - Moved end-of-sentence punctuation outside emphasis")
            changed = True

        if changed:
            changed_total += 1

    logger.info(f"2.1.6.3 - Done. Changes: {changed_total}")

    # 2.1.6.5 Avoid use of <em> or <strong> in description lists
    """
    2.1.6.5: Ikke bruk <em>/<strong> inni <dl> (gjelder både <dt> og <dd>).
    - Unwrapper <em>/<strong> under enhver <dl>, men rører ikke <code>/<pre>/<math> osv.
    - Idempotent.
    """
    logger.info("2.1.6.5 - Avoid use of <em>/<strong> in description lists")

    changed = 0
    for dl in soup.find_all("dl"):
        # Finn alle em/strong under denne DL, men hopp over dem som ligger inne i code/pre/math/…
        targets = []
        for node in dl.find_all(["em", "strong"]):
            if node.find_parent(_SKIP_INSIDE):
                continue
            targets.append(node)

        for node in targets:
            preview = (node.get_text(" ", strip=True) or "")[:60]
            node.unwrap()
            changed += 1
            if preview:
                logger.info(f'2.1.6.5 - Unwrapped emphasis in <dl>: "{preview}"')

    logger.info(f"2.1.6.5 - Done. Removed {changed} <em>/<strong> tag(s) inside <dl>.")
    
    # 2.1.6.6 Avoid use of <em> or <strong> in table headings
    logger.info('2.1.6.6 Avoid use of <em> or <strong> in table headings')
    for th in soup('th'):
        for emphasis in th(['em', 'strong']):
            logger.info(f'2.1.6.6 - Unwrapping emphasis in table heading: {emphasis}')
            emphasis.unwrap()

    '''
    # 2.1.6.7 Avoid use of <em> or <strong> in figures and figcaptions
    """
    2.1.6.7: Ikke bruk <em>/<strong> i figcaptions eller tekst uttrukket fra figurer.
    - Fjerner <em>/<strong> i (1) figcaptions og (2) 'figure text' containere.
    - Skipper <code>/<pre>/<math> osv.
    - Idempotent.
    """
    logger.info("2.1.6.7 - Avoid use of <em>/<strong> in figures and figcaptions")

    changed = 0

    # TODO: FIX NOW!
    # 1) figcaptions (og 'figcaption-like')
    is_figcaption_like = False
    is_figcaption_like |= el.name.lower() == "figcaption"
    is_figcaption_like |= (el.get("role") or "").lower() in ("doc-caption", "figure-caption")
    is_figcaption_like |= "caption" in (el.get("epub:type") or "").lower()
    
    figcaps = [el for el in soup.find_all(True) if is_figcaption_like]

    for cap in figcaps:
        targets = []
        for node in cap.find_all(["em", "strong"]):
            if node.find_parent(_SKIP_INSIDE):
                continue
            targets.append(node)

        for node in targets:
            preview = (node.get_text(" ", strip=True) or "")[:60]
            node.unwrap()
            changed += 1
            if preview:
                logger.info(f'2.1.6.7 - Unwrapped emphasis in figcaption: "{preview}"')

    # 2) tekst uttrukket fra figurer (fig-desc / figure-text / image-text)
    is_figure_text_extract = False
    is_figure_text_extract |= bool((classes := " ".join(el.get("class", []) or []).strip()) and _FIGTEXT_CLASS_RX.search(classes))
    is_figure_text_extract |= (el.get("data-type") or "").lower() in ("fig-desc", "figure-desc", "figure-text", "image-text")

    figtexts = [el for el in soup.find_all(True) if is_figure_text_extract]

    for box in figtexts:
        targets = []
        for node in box.find_all(["em", "strong"]):
            if node.find_parent(_SKIP_INSIDE):
                continue
            targets.append(node)

        for node in targets:
            preview = (node.get_text(" ", strip=True) or "")[:60]
            node.unwrap()
            changed += 1
            if preview:
                logger.info(f'2.1.6.7 - Unwrapped emphasis in extracted figure text: "{preview}"')

    logger.info(f"2.1.6.7 - Done. Removed {changed} <em>/<strong> tag(s).")
    '''


    """
    2.1.6.7: Ikke bruk <em>/<strong> i figcaptions eller tekst uttrukket fra figurer.
    - Fjerner <em>/<strong> i (1) figcaptions og (2) 'figure text' containere.
    - Skipper <code>/<pre>/<math> osv.
    - Idempotent.
    """
    logger.info("2.1.6.7 - Avoid use of <em>/<strong> in figures and figcaptions")

    def _is_figcaption_like(el) -> bool:
        if not getattr(el, "name", None):
            return False
        nm = el.name.lower()
        if nm == "figcaption":
            return True
        role = (el.get("role") or "").lower()
        if role in ("doc-caption", "figure-caption"):
            return True
        epubtype = (el.get("epub:type") or "").lower()
        if "caption" in epubtype:
            return True
        return False

    def _is_figure_text_extract(el) -> bool:
        if not getattr(el, "name", None):
            return False
        cls = " ".join(el.get("class", []) or []).strip()
        if cls and _FIGTEXT_CLASS_RX.search(cls):
            return True
        # enkelte produksjoner bruker data-attributter
        data_type = (el.get("data-type") or "").lower()
        if data_type in ("fig-desc", "figure-desc", "figure-text", "image-text"):
            return True
        return False


    changed = 0

    # 1) figcaptions (og 'figcaption-like')
    figcaps = [el for el in soup.find_all(True) if _is_figcaption_like(el)]
    for cap in figcaps:
        targets = []
        for node in cap.find_all(["em", "strong"]):
            if node.find_parent(_SKIP_INSIDE):
                continue
            targets.append(node)

        for node in targets:
            preview = (node.get_text(" ", strip=True) or "")[:60]
            node.unwrap()
            changed += 1
            if preview:
                logger.info(f'2.1.6.7 - Unwrapped emphasis in figcaption: "{preview}"')

    # 2) tekst uttrukket fra figurer (fig-desc / figure-text / image-text)
    figtexts = [el for el in soup.find_all(True) if _is_figure_text_extract(el)]
    for box in figtexts:
        targets = []
        for node in box.find_all(["em", "strong"]):
            if node.find_parent(_SKIP_INSIDE):
                continue
            targets.append(node)

        for node in targets:
            preview = (node.get_text(" ", strip=True) or "")[:60]
            node.unwrap()
            changed += 1
            if preview:
                logger.info(f'2.1.6.7 - Unwrapped emphasis in extracted figure text: "{preview}"')

    logger.info(f"2.1.6.7 - Done. Removed {changed} <em>/<strong> tag(s).")

    # 2.1.7 Non-breaking space

    """
    2.1.7 Non-breaking space:
    - Setter NBSP mellom symbol/forkortelse og tall (f.eks. '§ 12', 'kr 100').
    - Setter NBSP mellom tall og enhet/valuta (f.eks. '12 kg', '25 °C', '10 %').
    - Skipper kode/math/style/script/… og er idempotent.
    """
    logger.info('2.1.7 - Non-breaking space')

    changed = 0

    for text in list(soup(string=True)):
        if not isinstance(text, NavigableString):
            continue
        
        has_skipped_ancestor = False
        p = getattr(text, "parent", None)

        while p is not None:
            if getattr(p, "name", "").lower() in _SKIP_ANCESTORS:
                has_skipped_ancestor = True
            p = getattr(p, "parent", None)

        if has_skipped_ancestor or len(str(text)) < 2:
            continue

        s2 = RE_BEFORE.sub(rf'\1{NBSP}', str(text))
        s3 = RE_AFTER.sub(rf'{NBSP}\1', s2)

        if s3 != str(text):
            text.replace_with(NavigableString(s3))
            changed += 1

    logger.info(f"2.1.7 - Done. Updated {changed} text node(s).")

    # 2.1.8 Table of contents
    """
    2.1.8 Table of contents:
    - Fjern bilder i TOC.
    - Ikke bruk tabell for TOC; konverter til <ol> uten listepunkter.
    - Ikke bruk ALL CAPS i TOC-tekst (senk bare ord som er helt i versaler, unntatt akronymer).
    - Sørg for at sidehenvisningen ligger i den ANDRE <span class="lic">.
    """
    logger.info("2.1.8 - Table of contents")

    containers = []
    for el in soup.find_all(True):
        if _is_toc_container(el):
            containers.append(el)
    if not containers:
        logger.info("2.1.8 - No TOC container found.")
    else:
        total_fixed = 0
        for toc in containers:
            # fjern bilder
            imgs = toc.find_all("img")
            for im in imgs:
                im.decompose()

            # sikre listecontainer (og konverter tabell om nødvendig)
            ol, changed = _ensure_list_container(soup, toc)
            if changed:
                logger.info("2.1.8 - Converted TOC to <ol> list without bullets")

            # normaliser hver <li>
            fixed_here = 0
            for li in ol.find_all("li", recursive=False):
                if _normalize_toc_li(soup, li):
                    fixed_here += 1

            total_fixed += fixed_here
            logger.info(f"2.1.8 - Normalized {fixed_here} TOC item(s) in one container.")

        logger.info(f"2.1.8 - Done. Total TOC items normalized: {total_fixed}")
        
    # 2.1.8.1 TOC at the beginning of the book
    """
    2.1.8.1 TOC at the beginning of the book
    - Marker TOC-liste som <ol class="list-type-none list-style-type-none" style="list-style-type: none;">
    - Normaliser whitespace i TOC (multi-spaces -> enkel space)
    - Sørg for nøyaktig én space mellom <span class="lic">-elementer i <a>
    """
    logger.info("2.1.8.1 - TOC at the beginning of the book")

    tocs = [el for el in soup.find_all(True) if _is_toc_container(el)]
    if not tocs:
        logger.info("2.1.8.1 - No TOC container found.")

    else:
        processed = 0
        for toc in tocs:
            et = (toc.get("epub:type") or "").lower()
            if "frontmatter" not in et and "toc" in et:
                logger.warning(f"2.1.8.1 - TOC not marked as 'frontmatter' (epub:type='{et}').")

            # Finn toppnivå-liste
            ol = toc.find(["ol", "ul"], recursive=False)
            if ol is None:
                # prøv dypt
                ol = toc.find(["ol", "ul"])
                if ol is None:
                    logger.warning("2.1.8.1 - No list (<ol>/<ul>) found inside TOC; skipping container.")
                    continue

            # Konverter <ul> -> <ol> om nødvendig
            if ol.name != "ol":
                new_ol = soup.new_tag("ol")
                new_ol.extend(list(ol.contents))
                ol.replace_with(new_ol)
                ol = new_ol

            # Sett klasser og style (idempotent)
            cls = set(ol.get("class", []))
            cls.update({"list-type-none", "list-style-type-none"})
            ol["class"] = list(cls)
            style = (ol.get("style") or "").strip()
            # legg til 'list-style-type: none;' hvis ikke alt finnes fra før
            if "list-style-type:none;" not in style.replace(" ", "").lower():
                ol["style"] = (style + ("; " if style else "") + "list-style-type: none;").strip()

            # Whitespace-normalisering i TOC-tekster
            for t in toc.find_all(string=True):
                # ikke endre whitespace inne i <code>/<math> osv., men TOC bør ikke ha det uansett
                new_s = re.sub(r"[ \t]+", " ", str(t))
                if new_s != str(t):
                    t.replace_with(NavigableString(new_s))

            # Sørg for én space mellom <span class="lic"> i lenkene
            li_fixed = 0
            for li in ol.find_all("li", recursive=False):
                a = li.find("a", recursive=False) or li.find("a")
                if not a:
                    continue
                if _ensure_single_space_between_spans(a):
                    li_fixed += 1

            logger.info(f"2.1.8.1 - Normalized spacing for {li_fixed} TOC item(s).")
            processed += 1

        logger.info(f"2.1.8.1 - Done. Processed {processed} TOC container(s).")

    # 2.1.8.2 TOC at the beginning of each chapter
    """
    2.1.8.2: TOC i starten av hvert kapittel:
    - Finn lister nær kapittelstart som lenker internt i kapitlet.
    - Marker som <ol class="list-type-none" style="list-style-type: none;">.
    - Fjern bilder i kapittel-TOC.
    - Konverter tabeller til lister (uten sidetall-spans).
    - Normaliser evt. spacing mellom eksisterende <span class="lic"> (ingen påtvingelse av slike spans).
    """
    logger.info("2.1.8.2 - Chapter-level TOCs")

    chapters = _iter_chapter_like_containers(soup)
    total_lists = 0

    for chapter in chapters:
        # Kandidater: toppnivå UL/OL tidlig i kapitlet, samt tabeller som kan være minitoc
        candidates = []
        for el in chapter.find_all(["ul", "ol", "table"], recursive=False):
            candidates.append(el)
        # også litt dypere (noen ganger wrapper man i en div)
        if not candidates:
            for div in chapter.find_all("div", recursive=False):
                for el in div.find_all(["ul", "ol", "table"], recursive=False):
                    candidates.append(el)

        for cand in candidates:
            is_table = (cand.name == "table")
            list_el = None

            if is_table:
                # tabell-baserte mini-TOC: konverter med heuristikk
                # verifiser at den faktisk ser ut som kapittel-TOC: lenker til lokale ankere
                links = cand.find_all("a", href=True)
                if not links:
                    continue
                in_count = sum(1 for a in links if _anchor_in_container(chapter, _href_fragment(a)))
                if in_count == 0:
                    continue
                ol = soup.new_tag("ol", **{"class": "list-type-none"})
                ol["style"] = "list-style-type: none;"
                for tr in cand.find_all("tr"):
                    cells = tr.find_all(["td", "th"])
                    if not cells:
                        continue
                    label = " ".join(c.get_text(" ", strip=True) for c in cells).strip()
                    a = tr.find("a", href=True)
                    li = soup.new_tag("li")
                    link = soup.new_tag("a")
                    if a and a.get("href"):
                        link["href"] = a["href"]
                    link.string = label
                    li.append(link)
                    ol.append(li)
                cand.replace_with(ol)
                list_el = ol
            else:
                list_el = cand

            looks_like_chapter_toc = False
            """
            Heuristikk: en UL/OL nær kapittelstart hvor flertallet av lenkene peker til ankere i samme kapittel.
            """
            # må ligge tidlig i kapitlet (før 'max_scan' blokkbarn som ikke er whitespace)
            max_scan=8
            min_items=2
            ratio=0.6
            idx = 0
            for child in chapter.children:
                if not getattr(child, "name", None):
                    continue
                if child is list_el:
                    break
                idx += 1
                if idx > max_scan:
                    break
            if not looks_like_chapter_toc:
                links = list_el("a", href=True)
                if not looks_like_chapter_toc:
                    in_count = 0
                    for a in links:
                        frag = _href_fragment(a)
                        if frag and _anchor_in_container(chapter, frag):
                            in_count += 1

                    looks_like_chapter_toc = (in_count / max(1, len(links))) >= ratio

            # verifiser at liste-kandidaten faktisk er en kapittel-TOC
            if not looks_like_chapter_toc:
                continue

            # Sørg for <ol> + styling
            if list_el.name != "ol":
                new_ol = soup.new_tag("ol")
                new_ol.extend(list(list_el.contents))
                list_el.replace_with(new_ol)
                list_el = new_ol

            cls = set(list_el.get("class", []))
            cls.add("list-type-none")
            list_el["class"] = list(cls)
            style = (list_el.get("style") or "").strip()
            if "list-style-type:none;" not in style.replace(" ", "").lower():
                list_el["style"] = (style + ("; " if style else "") + "list-style-type: none;").strip()

            # Fjern bilder i mini-TOC
            for img in list_el.find_all("img"):
                img.decompose()

            # Normaliser spacing mellom evt. spans i lenkene (hvis produsert tidligere)
            fixed = 0
            for li in list_el.find_all("li", recursive=False):
                a = li.find("a", recursive=False) or li.find("a")
                if not a:
                    continue
                if _ensure_single_space_between_spans(a):
                    fixed += 1

            total_lists += 1
            logger.info(f"2.1.8.2 - Normalized chapter TOC list (items fixed for spacing: {fixed}).")

    logger.info(f"2.1.8.2 - Done. Chapter TOCs processed: {total_lists}")

    # 2.1.9 Backmatter
    
    # 2.1.9.1 Indexes and registers
    """
    2.1.9.1 Indexes and registers
    - Indeks/register i slutten av boka skal være listemarkup, ikke tabell.
    - Lister over bildekrediteringer i slutten av boka skal fjernes.
    """
    logger.info("2.1.9.1 - Indexes and registers")

    # 1) Fjern bildekrediteringer (konservativt)
    """
    Fjerner 'image/picture/photo/illustration credits' i bakstoff.
    Konservativ: krever backmatter OG treff på tydelig krediterings-overskrift,
    og fjerner seksjonen (heading + nærmeste liste/avsnitt) behørig.
    """
    removed = 0
    # Kandidater: seksjoner/div/aside i backmatter
    for box in soup(["section", "div", "aside"]):
        if not _is_backmatter_container(box):
            continue
        # Finn heading inni boksen
        head = box.find(re.compile(r'^h[1-6]$', re.I))
        if not head:
            continue
        title = head.get_text(" ", strip=True)
        if not _IMAGE_CREDITS_HEAD_RX.match(title):
            continue

        logger.info(f'2.1.9.1 - Removing image credits section: "{title}"')
        box.decompose()
        removed += 1

    # I enkelte bøker ligger kreditter som en løs liste med klasse/id
    for lst in soup.find_all(["ul", "ol"]):
        cls = " ".join(lst.get("class", [])).lower()
        el_id = (lst.get("id") or "").lower()
        if any(k in cls for k in ("image-credits", "illustration-credits", "picture-credits")) \
           or any(k in el_id for k in ("image-credits", "illustration-credits", "picture-credits")):
            if _is_backmatter_container(lst):
                logger.info('2.1.9.1 - Removing image credits list (class/id match near end).')
                lst.decompose()
                removed += 1

    if removed:
        pass
        logger.info(f"2.1.9.1 - Removed {removed} image credits section(s).")

    # 2) Finn indeks-/registercontainere og konverter tabeller til lister
    converted = 0

    def _is_index_container(el) -> bool:
        if not getattr(el, "name", None):
            return False
        et = (el.get("epub:type") or "").lower()
        if "index" in et:
            return True
        role = (el.get("role") or "").lower()
        if role in ("doc-index",):
            return True
        el_id = (el.get("id") or "").lower()
        if "index" in el_id or "register" in el_id:
            return True
        cls = " ".join(el.get("class", [])).lower()
        if "index" in cls or "register" in cls:
            return True
        # overskrift rett foran/inni
        head = el.find(re.compile(r'^h[1-6]$', re.I)) or el.find_previous(re.compile(r'^h[1-6]$', re.I))
        if head and _INDEX_HEAD_RX.match(head.get_text(" ", strip=True)):
            return True
        return False

    containers = [el for el in soup.find_all(True) if _is_index_container(el)]
    if not containers:
        logger.info("2.1.9.1 - No obvious index/register container found.")

    for box in containers:
        # Konverter bare tabeller (idempotent; kjøring #2 finner ingen tabeller)
        for table in list(box.find_all("table")):
            ol = soup.new_tag("ol", **{"class": "list-type-none"})
            ol["style"] = "list-style-type: none;"

            for tr in table("tr"):
                if (cells := tr(["td", "th"], recursive=False)):
                    continue
                li = soup.new_tag("li")
                first = True
                for cell in cells:
                    if not first:
                        li.append(NavigableString(" "))
                    first = False
                    # flytt cellens barn (bevar markup)
                    for n in list(cell.contents):
                        li.append(n.extract())
                ol.append(li)

            table.replace_with(ol)
            converted += 1

    logger.info(f"2.1.9.1 - Converted {converted} table(s) in index/register to lists.")


    # 2.1.9.2 Answer sections for tasks
    # "...any reference sections that follow" is not clear
    """
    2.1.9.2 Answer sections for tasks
    - Fjern/reloker 'task'-seksjoner fra backmatter.
    - La 'answer' (Fasit) og 'reference' stå igjen.
    - Andre ukjente seksjoner lar vi stå, men logger (konservativt).
    """
    logger.info("2.1.9.2 - Answer sections for tasks")
    llm = _ensure_llm_client(logger, use_llm) if use_llm else None

    def _classify_section(el, llm=None, logger=None):
        # PERF: move down
        """
        Returnerer 'task' | 'answer' | 'reference' | 'other'
        """
        types = _epub_types(el)
        title = _get_heading_text(el)

        # 1) epub:type-basert
        if types & TASK_TYPES:
            return "task"
        if types & ANSWER_TYPES:
            return "answer"
        if types & REF_TYPES:
            return "reference"

        # 2) overskrift-basert
        if title:
            if TASK_HEAD_RX.search(title):
                return "task"
            if ANSWER_HEAD_RX.search(title):
                return "answer"
            if REF_HEAD_RX.search(title):
                return "reference"

        # 3) valgfri LLM for uklart tilfelle
        if llm and getattr(llm, "available", False):
            try:
                excerpt = el.get_text(" ", strip=True)[:800]
                resp = llm._rpc({
                    "action": "classify_backmatter_section",
                    "title": title,
                    "epub_type": list(types),
                    "excerpt": excerpt
                })
                label = str(resp.get("label","other")).lower()
                if label in {"task","answer","reference","other"}:
                    return label
            except Exception as e:
                if logger: logger.warning(f"2.1.9.2 - LLM unavailable ({e}); continuing without it.")

        return "other"

    def _move_out_of_backmatter(section, backmatter, logger):
        """
        Flytt seksjon til forrige kapittel om mulig, ellers legg den rett før backmatter.
        Marker for idempotens med data-attributt.
        """
        if section.get("data-moved-from-backmatter") == "true":
            return False
        target = el.find_previous(lambda x:
                                  getattr(x, "name", None) and (
                                      "chapter" in (x.get("epub:type") or "").lower()
                                      or "chapter" in " ".join(x.get("class", [])).lower()
                                      or (x.get("role") or "").lower() in ("doc-chapter","chapter")
                                      )
                                  )
        section.extract()
        if target is not None:
            target.append(section)
            where = "previous chapter"
        else:
            backmatter.insert_before(section)
            where = "before backmatter"
        section["data-moved-from-backmatter"] = "true"
        title = _get_heading_text(section)
        logger.info(f'2.1.9.2 - Moved task section "{title or section.name}" to {where}.')
        return True

    if (backmatters := [el for el in soup.find_all(True) if _is_backmatter_container(el)]) is None:
        moved, kept_answer, kept_ref, kept_other = 0, 0, 0, 0

        for bm in backmatters:
            # Vi vurderer direkte blokkbarn som typisk er seksjoner i backmatter
            for child in list(bm.find_all(["section","article","div"], recursive=False)):
                label = _classify_section(child, llm=llm, logger=logger)
                if label == "task":
                    if _move_out_of_backmatter(child, bm, logger):
                        moved += 1
                    continue
                if label == "answer":
                    kept_answer += 1
                    continue
                if label == "reference":
                    kept_ref += 1
                    continue
                # annet: la stå, men si ifra – spesifikasjonen er vag om "any reference sections that follow"
                kept_other += 1
                title = _get_heading_text(child)
                logger.debug(f'2.1.9.2 - Keeping unknown backmatter section: "{title or child.name}" (types={_epub_types(child)})')

        logger.info(
            "2.1.9.2 - Done. Moved=%d, kept answers=%d, kept references=%d, kept other=%d",
            moved, kept_answer, kept_ref, kept_other
        )

    else:
        logger.info("2.1.9.2 - No backmatter container found.")

    # 2.1.10 Layout challenges
    """
    2.1.10 Layout challenges: flagg mistenkelige layouter for manuell avklaring.
    Endrer ikke DOM; logger bare WARN med korte utdrag.
    """
    logger.info("2.1.10 - Layout challenges (audit only)")
    llm = _ensure_llm_client(logger, use_llm) if use_llm else None

    issues = 0

    # 1) Umerkede lister/Dikt/Blokksitater i <p>/<div>
    for el in soup.find_all(["p","div","section","article"]):
        if not getattr(el, "name", None): continue
        # hopp tydelige semantikker
        if el.name in ("ol","ul","li","blockquote","table","figcaption"): continue

        try_list = False
        lines = _text_lines(el)
        if not len(lines) < 2:
            hits = sum(1 for ln in lines if LIST_LEADER_RX.match(ln))
            try_list |= hits >= max(2, len(lines)//2)

        try_poem = False
        lines = _text_lines(el)
        if not len(lines) < 3:
            if not sum(len(x) <= 60 for x in lines) / len(lines) < 0.7:
                if not sum(1 for ln in lines if LIST_LEADER_RX.match(ln)) > 0:
                    try_poem |= len(el.find_all("br")) >= 2

        try_quote = False
        if not el.find_parent("blockquote"):
            t = el.get_text(" ", strip=True)
            if (t := el.get_text(" ", strip=True)) and len(t) >= 12:
                try_quote |= bool(QUOTE_BORDER_RX.match(t)) or any(k in " ".join(el.get("class", [])).lower()
                                                                   for k in ("quote","sitat","citat"))

        label = None
        if use_llm and llm and (try_list or try_poem or try_quote):
            # La LLM gi oss en etikett for konfidens (valgfritt)
            try:
                resp = llm._rpc({
                    "action": "classify_layout_snippet",
                    "html": str(el)[:2000],
                    "text": el.get_text(" ", strip=True)[:800]
                })
                lab = str(resp.get("label","")).lower()
                conf = float(resp.get("confidence", 0.0))
                if lab in {"list","poem","blockquote"} and conf >= 0.6:
                    label = lab
            except Exception as e:
                logger.debug(f"2.1.10 - LLM unavailable ({e}); continuing without it.")

        if label == "list" or (label is None and try_list):
            logger.warning('2.1.10 [LIST?] %s — "%s"', _css_path(el), _snippet(el))
            issues += 1
        if label == "poem" or (label is None and try_poem):
            logger.warning('2.1.10 [POEM?] %s — "%s"', _css_path(el), _snippet(el))
            issues += 1
        if label == "blockquote" or (label is None and try_quote):
            logger.warning('2.1.10 [BLOCKQUOTE?] %s — "%s"', _css_path(el), _snippet(el))
            issues += 1

    # 2) Layout-tabeller
    for tbl in soup.find_all("table"):
        is_layout_table = False
        if not tbl.find("th"):
            role = (tbl.get("role") or "").lower()
            if role in ("presentation","none"):
                is_layout_table = True
            else:
                has_style = bool(SUSPECT_STYLE_RX.search(tbl.get("style") or "")) or any(
                    any(attr in (el.get("style") or "").lower() for attr in ("width", "position", "float"))
                    for el in tbl.find_all(True)
                )
                many_rows = len(tbl.find_all("tr")) >= 3 and len(tbl.find_all("td")) >= 6
                is_layout_table = has_style or many_rows

        if is_layout_table:
            logger.warning('2.1.10 [LAYOUT-TABLE?] %s — rows=%d, cells=%d',
                           _css_path(tbl),
                           len(tbl.find_all("tr")),
                           len(tbl.find_all("td")))
            issues += 1

    # 3) Suspekt inline-CSS
    for el in soup.find_all(True, style=True):
        if bool(SUSPECT_STYLE_RX.search((el.get("style") or ""))):
            logger.warning('2.1.10 [INLINE-CSS?] %s — style="%s"',
                           _css_path(el), (el.get("style") or "").strip()[:120])
            issues += 1

    # 4) Overbruk av <br>
    for p in soup.find_all("p"):
        brs = p.find_all("br")
        if len(brs) >= 3:
            logger.warning('2.1.10 [MANY <br>?] %s — %d <br> — "%s"',
                           _css_path(p), len(brs), _snippet(p))
            issues += 1

    logger.info("2.1.10 - Audit complete. Potential issues flagged: %d", issues)

    # 2.1.11 Use of <hr> or <br>
    """
    2.1.11 Use of <hr> or <br>
    - Fjern <hr> overalt (jf. 'avoid the use of <hr> to represent purely visual effects').
    - Behold <br> KUN i listekontekst (li/dt/dd). Utenfor lister: fjern, og sett inn én space der nødvendig.
    - I lister: kollaps flere <br> på rad til én.
    - Skipp pre/code/math/script/style/textarea.
    """
    logger.info("2.1.11 - Use of <hr> or <br>")

    removed_hr = 0
    fixed_br   = 0
    kept_br    = 0

    def _in_protected_context(node):
        p = node
        while p is not None:
            if getattr(p, "name", "").lower() in _PROTECTED:
                return True
            p = p.parent
        return False

    # 1) <hr> – fjern, unntatt beskyttede kontekster (burde ikke finnes der uansett)
    for hr in list(soup.find_all("hr")):
        if _in_protected_context(hr):
            continue
        hr.decompose()
        removed_hr += 1

    # 2) <br>
    for br in list(soup.find_all("br")):
        if _in_protected_context(br):
            continue

        in_list_context = False
        p = br.parent
        while p is not None:
            if getattr(p, "name", "").lower() in ("li", "dt", "dd"):
                in_list_context = True
                break
            if p == soup:
                break
            p = p.parent

        if in_list_context:
            # i liste: la én <br> stå, men fjern duplikater på rad
            # (idempotent: kjøring #2 finner ingen flere)
            nxt = br.next_sibling
            while getattr(nxt, "name", None) == "br":
                kill = nxt
                nxt = nxt.next_sibling
                kill.decompose()
                fixed_br += 1
            kept_br += 1
            continue

        # utenfor lister: erstatt med space hvis nødvendig, ellers fjern
        needs_space_around = False
        left = br.previous_sibling
        right = br.next_sibling
        left_ws = isinstance(left, NavigableString) and left and left[-1].isspace()
        right_ws = isinstance(right, NavigableString) and right and right[:1].isspace()
        needs_space_around = not (left_ws or right_ws)

        if needs_space_around:
            br.replace_with(NavigableString(" "))
        else:
            br.decompose()
        fixed_br += 1

    logger.info("2.1.11 - Done. Removed hr=%d, fixed br=%d, kept br in lists=%d",
                removed_hr, fixed_br, kept_br)

    # 2.1.11.1 Use of <br> in mathematics books
    """
    2.1.11.1: I matematikkbøker, bruk <br> for linjeskift:
      - mellom tekst og utregning (<math>), og
      - mellom to påfølgende utregninger (<math> … <math>).
    Idempotent; endrer ikke protected kontekster.
    """
    logger.info('2.1.11.1 - Use of <br> in mathematics books')
    if not args.mathematics:
        logger.info("2.1.11.1 - Not a mathematics book; skipping.")
    else:
        inserted = 0
        collapsed = 0

        for m in soup.find_all("math"):
            if _in_protected(m):   # (math inni math/skript er uansett uaktuelt, men safe guard)
                continue

            prev = m.previous_sibling
            # TODO: make more robust
            while prev is not None and isinstance(prev, NavigableString) and not prev.strip():
                prev = prev.previous_sibling
            if (prev and
                not getattr(prev, "name", None) == "br" and
                getattr(prev, "name", "").lower() == "math" or _has_alnum_text(prev)
                ):
                m.insert_before(soup.new_tag("br"))
                inserted += 1
    
            nxt = m.next_sibling
            while nxt is not None and isinstance(nxt, NavigableString) and not nxt.strip():
                nxt = nxt.next_sibling
            if (nxt and
                not getattr(nxt, "name", None) == "br" and
                (getattr(nxt, "name", "").lower() == "math" or _has_alnum_text(nxt))
                ):
                m.insert_after(soup.new_tag("br"))
                inserted += 1

            # Rydd opp doble <br> rundt denne math’en
            parent = m.parent
            if parent:
                collapsed += _collapse_adjacent_brs(parent)

        logger.info("2.1.11.1 - Done. Inserted br=%d, collapsed duplicates=%d", inserted, collapsed)

    # 2.1.12 OCR
    # This requirement is not implementable
    """
    2.1.12 OCR – Audit only.
    - Samler tokens og flagger mistenkelige OCR-mønstre (O↔0, I/l↔1, rn↔m, uventet alfa+digit).
    - Logger estimert 'risikoandel' (IKKE nøyaktig feilrate).
    - Logger også noder med ikke-NFC (uten å endre).
    - Valgfritt: bruk LLM til å bekrefte et lite utvalg funn.
    """
    logger.info("2.1.12 - OCR (audit)")

    total_tokens, samples = _collect_tokens(soup)
    if total_tokens == 0:
        logger.info("2.1.12 - No tokens found; skipping audit.")

    else:
        suspicious = []
        nfc_nodes_logged = set()

        # Finn ikke-NFC noder for info
        for t in soup.find_all(string=True):
            if not isinstance(t, NavigableString) or _in_protected(t):
                continue
            s = str(t)
            if unicodedata.normalize("NFC", s) != s and id(t) not in nfc_nodes_logged:
                nfc_nodes_logged.add(id(t))
                nfc_path = _css_path(t.parent) if getattr(t, "parent", None) else "<orphan>"
                logger.warning('2.1.12 - Non-NFC text at %s: "%s"', nfc_path, s[:120].replace("\n", " "))

        # Heuristisk mistenkelige tokens
        for tok, node, ctx in samples:
            bad, reason = _is_suspicious_token(tok)
            if bad:
                suspicious.append((tok, reason, node, ctx))
            if len(suspicious) >= 300:
                break  # begrens logg

        # Valgfri LLM: bekreft et lite utvalg (reduser falske positiver)
        llm_confirmed = 0
        if use_llm and suspicious:
            try:
                llm = _ensure_llm_client(logger, use_llm=True)
                subset = suspicious[:50]  # spør om et lite utvalg
                for tok, reason, node, ctx in subset:
                    try:
                        resp = llm._rpc({
                            "action": "ocr_token_check",
                            "token": tok,
                            "context": ctx
                        })
                        if bool(resp.get("likely_error", False)):
                            llm_confirmed += 1
                    except Exception:
                        pass
            except Exception as e:
                logger.warning(f"2.1.12 - LLM unavailable ({e}); continuing without LLM).")

        # Grovt risikomål (ikke en feilrate!)
        risk = len(suspicious) / max(1, total_tokens)
        logger.info("2.1.12 - Tokens scanned: %d, suspicious (heuristic): %d (%.5f)",
                    total_tokens, len(suspicious), risk)

        if use_llm and suspicious:
            logger.info("2.1.12 - LLM confirmed suspicious subset: %d/%d", llm_confirmed, min(50, len(suspicious)))

        # Logg konkrete smaksprøver
        for i, (tok, reason, node, ctx) in enumerate(suspicious[:30], 1):
            ctx_path = _css_path(node.parent) if getattr(node, "parent", None) else "<orphan>"
            logger.warning('2.1.12 - Suspicious token #%d [%s] at %s: token="%s", context="…%s…" ',
                           i, reason, ctx_path, tok, ctx.replace("\n", " ")[:140])

        if risk > 0.001:  # 0.1% heuristisk terskel (99.9%) – strengere enn 99.95% for å få tidlig varsling
            logger.warning("2.1.12 - Heuristic OCR risk above threshold (%.3f%%). Review recommended.",
                           100*risk)

        logger.info("2.1.12 - Audit complete (no DOM changes).")

    # 2.2 Thematic grouping of content
    """
    2.2 Thematic grouping of content
    Wrap hver overskrift (h1–h6) og innholdet frem til neste overskrift med
    likt eller høyere nivå i en <section>. Idempotent.

    - Bevarer headingens id/innhold og flytter med på plass.
    - Setter aria-labelledby på section hvis heading har id.
    - Lager section-id basert på heading-id (sec-<id>), uten kollisjon.
    - Hopper over <nav>, <figcaption>, <table>/<thead>/<tbody>/<tfoot>.
    """

    logger.info("2.2 - Thematic grouping of content")
    headings = list(soup.find_all(re.compile(r'^h[1-6]$', re.I)))
    created = 0
    adjusted = 0

    for h in headings:
        sec = h.find_parent("section")

        # Hvis vi er inne i en kapittel-seksjon: ikke pakk rundt, bare justér den
        if sec and _is_chapter_section(sec):
            # Flytt eventuell pagebreak som står før heading inni samme section, ut foran section
            first = _first_significant_child(sec)
            if first is not h and _is_pagebreak(first):
                first.extract()
                sec.insert_before(first)
                adjusted += 1
                logger.info('2.2 - Moved pagebreak before chapter section to make heading first child.')

            # Sørg for aria-labelledby på kapittel-seksjonen
            hid = h.get("id")
            if hid and sec.get("aria-labelledby") != hid:
                sec["aria-labelledby"] = hid
                adjusted += 1
                logger.info('2.2 - Set aria-labelledby="%s" on chapter section.', hid)

            # Ikke lag en ny auto-section
            continue

        # Hvis allerede korrekt seksjonert, hopp videre
        if _already_sectioned(h):
            continue

        # Ellers: vanlig auto-wrapping rundt headingen
        auto = soup.new_tag("section")
        auto["data-auto-section"] = "true"
        hid = h.get("id")
        if hid:
            auto["aria-labelledby"] = hid
            # gi unik id basert på heading-id
            base = f"sec-{hid}"
            sid, i = base, 1
            while soup.find(id=sid):
                i += 1
                sid = f"{base}-{i}"
            auto["id"] = sid

        # sett inn auto-section som søsken der headingen lå
        h.insert_before(auto)
        auto.append(h.extract())

        # flytt etterfølgende søsken til auto-section til neste heading med nivå <=
        this_level = int(h.name[1])
        sib = auto.next_sibling
        while sib is not None:
            nxt = sib.next_sibling
            is_heading = re.match(r'^h([1-6])$', getattr(sib, "name", "") or "", re.I)
            if is_heading and int(sib.name[1]) <= this_level:
                break
            auto.append(sib.extract())
            sib = nxt

        created += 1
        logger.info('2.2 - Created auto <section> for "%s".',
                    (h.get_text(" ", strip=True) or "")[:80])

    # Flate ut overflødige wrapper-seksjoner til slutt
    flattened = _flatten_redundant_sections(soup, logger)

    logger.info(
        "2.2 - Done. Auto sections created: %d, chapter sections adjusted: %d, redundant sections flattened: %d",
        created, adjusted, flattened
    )

    # 2.2.1 Use of section within tasks
    # TODO: check <p epub:type="bridgehead">Oppgaver</p> as in 863500
    """
    2.2.1 Use of section within tasks
    - Når enkeltoppgaver har egen heading: pakk hver oppgave i sin egen <section>.
    - Rør ikke rene 'container'-seksjoner (assessments/exercises/tasks) – vi går på de enkelte elementene.
    - Idempotent; flater ut overflødige wrapper-seksjoner etterpå.
    """
    logger.info("2.2.1 - Use of <section> within tasks")

    wrapped = 0
    skipped_no_heading = 0
    already_ok = 0

    # Kandidater: alle elementer med epub:type som inneholder task-item-type
    candidates = [el for el in soup.find_all(True)
                  if _epub_types(el) and _is_task_item(el)]

    for el in candidates:
        # Hopp rene kapittel/”container”-noder (assessments/exercises/tasks)
        if _is_task_container(el):
            continue

        # Hvis allerede korrekt <section> rundt, hopp
        if _already_task_section(el):
            already_ok += 1
            continue

        # Krev heading inni oppgaven (spesifikasjonen sier "when individual tasks have headings")
        if not _has_heading_in(el):
            skipped_no_heading += 1
            continue

        # Wrap
        if _wrap_as_task_section(soup, el, logger):
            wrapped += 1

    # Rydd opp tomme wrapper-sections
    flattened = _flatten_redundant_sections(soup, logger)

    logger.info(
        "2.2.1 - Done. Wrapped=%d, already_ok=%d, skipped(no heading)=%d, flattened=%d",
        wrapped, already_ok, skipped_no_heading, flattened
    )

    # 2.3 Figures/Images
    
    # 2.3.1 Alt tag

    """
    2.3.1 Alt tag
    - Sørg for at alle <img> har alt med én av: photo|illustration|figure|symbol|map|drawing|comic|logo
    - Fyll inn hvis alt mangler/er søppel. Bevar gode eksisterende ALT-tekster.
    - Normaliser eksisterende generiske ALT til lowercase.
    """
    logger.info("2.3.1 - Alt tag")

    fixed, normalized, kept = 0, 0, 0

    for img in soup.find_all("img"):
        # Skip tydelig dekorative? Spesifikasjonen ber om generiske verdier, ikke alt=""
        # Så vi fyller likevel – ingen skip her med mindre helt skjult.
        if img.get("aria-hidden") == "true":
            # likevel: sett symbol for konsistens? Vi lar dem stå urørt.
            kept += 1
            continue

        alt = img.get("alt")
        src = img.get("src", "")

        # Allerede en tillatt generisk verdi -> normaliser til lowercase
        if isinstance(alt, str) and alt.strip().lower() in _ALLOWED_ALTS:
            low = alt.strip().lower()
            if alt != low:
                img["alt"] = low
                normalized += 1
            else:
                kept += 1
            continue

        # Hvis alt finnes og ser ut som ekte beskrivende tekst → behold
        if isinstance(alt, str) and not _is_junk_alt(alt, src):
            kept += 1
            continue

        # Sett generisk alt
        label = _classify_generic_alt(img)
        img["alt"] = label
        fixed += 1
        logger.info('2.3.1 - Set alt="%s" for <img src="%s">', label, src[:120])

    logger.info("2.3.1 - Done. Set=%d, normalized=%d, kept=%d", fixed, normalized, kept)

    # 2.3.2 Extraction of text in figures
    """
    2.3.2 Extraction of text in figures (med dummy-LLM/OCR-støtte)

    - Matematikkbok: fjern all figur-tekst (aside.fig-desc).
    - Vanlig bok:
        * Ikke trekk ut / fjern tekst for foto/kart/graf/screenshot/bokside (jf. heuristikk).
        * Behold og normaliser figur-tekst for øvrige figurer.
        * Hvis figur-tekst mangler/er tom og use_llm=True OG ocr_rpc gitt:
          kall ocr_rpc(image_path) og fyll inn resultat.
    - Idempotent; nye bokser merkes med data-ocr="true" og lister med data-auto-list="true".

    Parametre:
      - use_llm: Kun et flagg. Hvis ikke True -> ingen OCR-forsøk.
      - input_base_dir: Rotmappe for å slå opp <img src>. Hvis None -> ingen OCR.
      - ocr_rpc: callable(image_path:str) -> Optional[str]. Hvis None -> ingen OCR.
    """

    input_base_dir: str | None = None # TODO: args.input_base_dir
    is_mathematics_book: bool = bool(args.mathematics)
    use_llm: bool = bool(args.llm)
    ocr_rpc: callable | None = None

    def _resolve_image_path(src: str, base_dir: str) -> str | None:
        if not src or not base_dir:
            return None
        rel = unquote(urlparse(src).path or src).lstrip("./")
        cand = path.join(base_dir, rel)
        return cand if path.exists(cand) else None

    logger.info("2.3.2 - Extraction of text in figures")

    ocr_enabled = bool(use_llm) and callable(ocr_rpc) and bool(input_base_dir)
    if not ocr_enabled:
        logger.debug("2.3.2 - OCR disabled (use_llm=%s, ocr_rpc=%s, input_base_dir=%s)",
                     bool(use_llm), bool(callable(ocr_rpc)), bool(input_base_dir))

    removed = 0
    normalized = 0
    ocred = 0

    for fig in soup.find_all("figure"):
        if _in_protected(fig):
            continue

        img = fig.find("img")
        if not img:
            # Ren tekstfigur – ikke noe å OCR-e
            # Normaliser ev. eksisterende boks
            box = fig.find("aside", class_="fig-desc", recursive=False)
            if box and not _fig_text_box_is_empty(box):
                if _normalize_figure_text_box(soup, box, logger):
                    normalized += 1
            continue

        # 1) Matematikkbøker: fjern alltid figur-tekst
        if is_mathematics_book:
            for cand in list(fig.find_all("aside", class_="fig-desc", recursive=False)):
                cand.decompose(); removed += 1
            sib = fig.find_next_sibling()
            if sib and "fig-desc" in (sib.get("class") or []):
                sib.decompose(); removed += 1
            continue

        # 2) Ikke trekk ut tekst fra typer vi skal hoppe over (foto/kart/diagram/…)
        if _should_never_extract_text_for(img):
            for cand in list(fig.find_all("aside", class_="fig-desc", recursive=False)):
                cand.decompose(); removed += 1
            sib = fig.find_next_sibling()
            if sib and "fig-desc" in (sib.get("class") or []):
                sib.decompose(); removed += 1
            continue

        # 3) Finn eksisterende fig-tekstboks (barn eller umiddelbar søsken)
        box = fig.find("aside", class_="fig-desc", recursive=False)
        if not box:
            sib = fig.find_next_sibling()
            if sib and "fig-desc" in (sib.get("class") or []):
                box = sib

        # 4) Hvis boks finnes med innhold → normaliser
        if box and not _fig_text_box_is_empty(box):
            if _normalize_figure_text_box(soup, box, logger):
                normalized += 1
            continue

        # 5) Mangler/er tom boks → prøv OCR kun hvis eksplisitt aktivert og mulig
        if ocr_enabled:
            img_path = _resolve_image_path(img.get("src"), input_base_dir)
            if not img_path:
                logger.debug("2.3.2 - Could not resolve image path for OCR: %s", img.get("src"))
                continue

            try:
                text = ocr_rpc(img_path)  # forventer Optional[str]
            except Exception as e:
                logger.warning("2.3.2 - OCR RPC failed for %s: %s", img_path, e)
                text = None

            if text:
                # Opprett/bruk boks
                if not box:
                    box = _find_or_create_fig_text_box(soup, fig)
                # Tøm og fyll inn
                for c in list(box.contents):
                    c.extract()
                t = text.strip()
                if not t:
                    continue
                if len(t) <= 80 and t.count(".") <= 1 and len(t.split()) <= 12:
                    box.append(NavigableString(t))
                else:
                    p = soup.new_tag("p"); p.string = t
                    box.append(p)
                box["data-ocr"] = "true"
                ocred += 1
                # Rydd etterpå
                _normalize_figure_text_box(soup, box, logger)

    logger.info("2.3.2 - Done. Removed boxes=%d, normalized boxes=%d, OCR-added boxes=%d",
                removed, normalized, ocred)

    # 2.3.2.1 Extraction of text from figures in mathematics books
    """
    2.3.2.1 Extraction of text from figures in mathematics books
    - I mattebøker skal tekst fra figurer ikke med – behold kun selve bildet (+ ev. figcaption).
    - Fjerner figurbokser som inneholder uttrukket tekst (aside.fig-desc o.l.), både som barn av
      <figure> og som umiddelbar søsken etter <figure>.
    - Idempotent.
    """
    logger.info("2.3.2.1 - Extraction of text from figures in mathematics books")
    if not is_mathematics_book:
        logger.info("2.3.2.1 - Not a mathematics book; skipping.")

    else:
        removed = 0
        for fig in soup.find_all("figure"):
            # Fjern fig-tekstbokser som barn (behold figcaption)
            for child in list(fig.find_all(True, recursive=False)):
                if _is_fig_text_container(child):
                    child.decompose()
                    removed += 1

            # Fjern umiddelbar søsken-boks (noen produksjoner legger fig-tekst etter figure)
            sib = _next_significant_sibling(fig)
            if sib is not None and _is_fig_text_container(sib):
                sib.decompose()
                removed += 1

            # Safe-guard: fjern ev. rester som er merket data-ocr/data-auto-list inne i figure (ikke figcaption)
            for inner in list(fig.find_all(True)):
                if inner.name == "figcaption":
                    continue
                if inner.get("data-ocr") == "true" or inner.get("data-auto-list") == "true":
                    inner.decompose()
                    removed += 1

        logger.info("2.3.2.1 - Done. Removed figure-text boxes: %d", removed)

    # 2.3.3 Aside element for image description to be added later
    """
    2.3.3 Aside element for image description to be added later (rask/idempotent)
    - For hver <figure> som har minst én <img> med ikke-tom alt:
      sørg for <aside class="prodnote" epub:type="z3998:production" id="desc-…">¤</aside>
    - Normaliser eksisterende bokser (klassse/innhold/id).
    - Bruk O(1) id-generering basert på forhåndsinnsamlet used_ids.
    """
    logger.info("2.3.3 - Aside element for image description (prodnote)")

    # 1) Samle alle brukte id-er én gang (O(N))
    used_ids = {el.get("id") for el in soup.find_all(True, id=True)}
    used_ids.discard(None)

    # Teller per base for å slippe kollisjonsløkker
    counters = {}

    def _sanitize_base(base: str) -> str:
        # enkle id-vennlige tegn
        base = re.sub(r"\s+", "-", base.strip()) if base else "desc"
        base = re.sub(r"[^A-Za-z0-9\-\._:]", "-", base)
        return base or "desc"

    def alloc_id(base: str) -> str:
        """
        Rask, kollisjonsfri id-allokator uten soup.find() i løkke.
        - Foretrekker 'base' hvis ledig, ellers 'base-2', 'base-3', ...
        - Oppdaterer used_ids fortløpende.
        """
        base = _sanitize_base(base)
        if base not in used_ids:
            used_ids.add(base)
            return base
        n = counters.get(base, 2)
        cand = f"{base}-{n}"
        while cand in used_ids:
            n += 1
            cand = f"{base}-{n}"
        counters[base] = n + 1  # neste gang starter vi på neste tall
        used_ids.add(cand)
        return cand

    added = normalized = 0

    figures = soup.find_all("figure")
    for fig in figures:
        # Har figuren minst én <img> med ikke-tom alt?
        imgs = fig.find_all("img")
        if not imgs:
            continue
        img0 = next((im for im in imgs if isinstance(im.get("alt"), str) and im["alt"].strip()), None)
        if not img0:
            continue

        # Finn eksisterende prodnote i figuren (direkte barn foretrekkes)
        existing = None
        for child in fig.find_all("aside", recursive=False):
            et = (child.get("epub:type") or "").lower()
            if et == "z3998:production":
                existing = child
                break
        if not existing:
            # Noen produksjoner legger boksen rett etter figure
            sib = fig.find_next_sibling()
            if sib and (sib.get("epub:type") or "").lower() == "z3998:production":
                existing = sib

        base = f"desc-{(img0.get('id') or fig.get('id') or 'desc')}"

        if existing:
            # Sett korrekt klasse
            classes = set(existing.get("class", []))
            if "prodnote" not in classes or len(classes) != 1:
                existing["class"] = ["prodnote"]
                normalized += 1

            # Sett korrekt innhold '¤'
            # Unngå dyr get_text – sjekk raskt: en enkelt NavigableString med '¤'
            ok_content = (len(existing.contents) == 1 and
                          isinstance(existing.contents[0], NavigableString) and
                          existing.contents[0].strip() == "¤")
            if not ok_content:
                existing.clear()
                existing.append("¤")
                normalized += 1

            # Sørg for unik id
            cur_id = existing.get("id")
            if not cur_id or cur_id in used_ids and sum(1 for _ in soup.find_all(id=cur_id)) > 1:
                new_id = alloc_id(base)
                existing["id"] = new_id
                normalized += 1
            else:
                # Reservér eksisterende id så vi ikke gjenbruker den
                used_ids.add(cur_id)

            continue

        # Opprett ny prodnote
        aside = soup.new_tag("aside")
        aside["class"] = ["prodnote"]
        aside["epub:type"] = "z3998:production"
        aside["id"] = alloc_id(base)
        aside.append("¤")
        fig.append(aside)
        added += 1

    logger.info("2.3.3 - Done. Added=%d, normalized=%d", added, normalized)

    # 2.3.4 Figcaptions
    """
    2.3.4 Figcaptions
    - Unwrap <em>/<strong> i figcaptions
    - Fjern tomme <p>
    - Unwrap én enkelt toppnivå-<p> (uten attrs) hvis den er eneste barn (unødvendig <p>)
    - Ikke rør ved blokkelement-strukturer
    - Idempotent
    """
    logger.info("2.3.4 - Figcaptions")

    removed_emstrong = 0
    removed_empty_p = 0
    single_unwrapped = 0
    ws_normalized = 0

    for fc in soup.find_all("figcaption"):
        if _in_protected(fc):
            continue

        # 1) Fjern em/strong
        for tag in list(fc.find_all(["em", "strong"])):
            tag.unwrap()
            removed_emstrong += 1

        # 2) Fjern tomme <p>
        for p in list(fc.find_all("p")):
            if not p.get_text(strip=True):
                p.decompose()
                removed_empty_p += 1

        # 3) Unwrap én unødvendig toppnivå-<p>
        #    (kun når akkurat én <p> er direkte barn og den ikke har attrs/blokker)
        direct_ps = [c for c in fc.contents if getattr(c, "name", "") == "p"]
        if len(direct_ps) == 1:
            p = direct_ps[0]
            if not p.attrs and not p.find(_BLOCKY):
                p.unwrap()
                single_unwrapped += 1
        else:
            # Hvis det finnes blokkelementer i figcaption, la strukturen være
            pass

        # 4) (Valgfritt) lett whitespace-normalisering i tekstnoder
        for t in fc.find_all(string=True):
            if isinstance(t, NavigableString):
                s = str(t)
                ns = re.sub(r"\s+", " ", s)
                if ns != s:
                    t.replace_with(NavigableString(ns))
                    ws_normalized += 1

    logger.info(
        "2.3.4 - Done. removed <em>/<strong>=%d, removed empty <p>=%d, unwrapped single <p>=%d, ws-normalized-nodes=%d",
        removed_emstrong, removed_empty_p, single_unwrapped, ws_normalized
    )

    # 2.3.5 Placement of figure elements
    """
    2.3.5 Placement of figure elements
    - Flytt figurer til rett før tasks/andre relokerte elementer, ellers til slutten av seksjonen.
    - Ikke flytt i matematikkbøker.
    - Idempotent; bevarer rekkefølge; rører kun toppnivå-figurer i <section>.
    """
    logger.info("2.3.5 - Placement of figure elements")

    if not args.relocate:
        logger.info("2.3.5 - Relocation disabled (--no-relocate).")
    elif args.mathematics or args.science: # Covers 2.3.6
        logger.info("2.3.5 - Mathematics book; figures are not relocated.")
    else:
        moved_total = 0
        sections = soup.find_all("section")
        for sec in sections:
            # hopp spesielle seksjoner hvis dere ønsker (nav/TOC/backmatter kan filtreres her)
            # Finn direkte barn (signifikante)
            kids = _significant_children(sec)
            if not kids:
                continue

            # Finn alle toppnivå-figurer (ikke inne i tasks/andre containere)
            figs = [k for k in kids if getattr(k, "name", "") == "figure" and not _in_task_ancestor(k)]
            if not figs:
                continue

            # Finn "anker": første task-blokk ELLER annet relokert element
            anchor_idx = None
            for idx, k in enumerate(kids):
                if _is_taskish(k) or _is_other_relocated(k):
                    anchor_idx = idx
                    break
            if anchor_idx is None:
                # ingen anchor → plasser på slutten
                anchor_idx = len(kids)

            # Sjekk om figurene allerede ligger som sammenhengende blokk rett før anker
            # (idempotens: hvis sant, ikke gjør noe)
            expected_block = figs
            block_len = len(expected_block)
            already_ok = False
            if block_len > 0:
                start = max(0, anchor_idx - block_len)
                slice_block = kids[start:anchor_idx]
                already_ok = slice_block == expected_block

            if already_ok:
                continue  # alt riktig plassert i denne seksjonen

            # Ellers: flytt alle figurene i opprinnelig rekkefølge til rett før anker
            # Oppdater 'kids' etter hvert move kan være dyrt; vi bygger mål og flytter i én omgang.
            # Forankre innsettingspunkt:
            anchor_node = kids[anchor_idx] if anchor_idx < len(kids) else None

            # Ekstra: bevare rekkefølge som de står i dokumentet nå
            for fig in figs:
                # hopp figurer som allerede står rett før anchor i riktig rekkefølge – men enkel, vi flytter uansett
                fig.extract()
                if anchor_node is not None:
                    anchor_node.insert_before(fig)
                else:
                    sec.append(fig)
                # merk som relokert (kan hjelpe 2.1.2-ordning)
                fig["data-relocated-figure"] = "true"
                moved_total += 1

        logger.info("2.3.5 - Done. Figures moved: %d", moved_total)

    # 2.3.5.1 Figures at the start of each chapter, placed before the chapter heading
    """
    2.3.5.1 Figures at the start of each chapter, placed before the chapter heading
    - Flytt figurer mellom (pagebreak før heading) og (heading) til bunnen av heading-siden
      (rett før neste pagebreak etter heading).
    - Sett inn "<p>Kapittelbildet er flyttet til neste side.</p>" på den nå tomme siden.
    - Ikke flytt i matematikkbøker.
    - Idempotent via data-relocated-chapter-figure="true".
    """
    logger.info("2.3.5.1 - Figures before chapter headings")

    if not args.relocate:
        logger.info("2.3.5.1 - Relocation disabled (--no-relocate).")
    elif args.mathematics:
        logger.info("2.3.5.1 - Mathematics book; figures are not relocated.")
    else:
        moved = 0
        inserted_msgs = 0

        # Finn alle kapittel-seksjoner
        for sec in soup.find_all("section"):
            if not _is_chapter_section(sec):
                continue

            # Finn første heading i kapittel-seksjonen
            h = None
            # prioriter første signifikante barn som heading
            candidate = _first_significant_child(sec)
            if candidate is not None and _HEADING_RX.match(getattr(candidate, "name", "") or ""):
                h = candidate
            else:
                h = sec.find(_HEADING_RX)
            if not h:
                continue

            # Finn pagebreak rett før og rett etter heading (på samme nivå av søsken)
            pb_before = _find_prev_pagebreak_sibling(h)
            pb_after  = _find_next_pagebreak_sibling(h)

            # Vi trenger minst pb_before for å vite at heading starter ny side
            if not pb_before:
                continue

            # Finn figurer mellom pb_before og heading (toppnivå i samme parent)
            between = _significant_between(pb_before, h)
            figs_to_move = [n for n in between if getattr(n, "name", "") == "figure" and n.get("data-relocated-chapter-figure") != "true"]

            if not figs_to_move:
                # Ingenting å flytte
                continue

            # Sett inn figurer nederst på heading-siden: rett før pb_after (hvis finnes),
            # ellers på slutten av seksjonen
            insert_anchor = pb_after if pb_after is not None else sec.contents[-1] if sec.contents else sec
            for fig in figs_to_move:
                fig.extract()
                if pb_after is not None:
                    pb_after.insert_before(fig)
                else:
                    sec.append(fig)
                fig["data-relocated-chapter-figure"] = "true"
                moved += 1

            # Sjekk om siden mellom pb_before og heading er blitt tom for signifikante noder
            remaining = _significant_between(pb_before, h)
            has_message = any(
                getattr(n, "name", "") == "p" and (n.get_text(" ", strip=True) or "") == "Kapittelbildet er flyttet til neste side."
                for n in remaining
            )
            if not remaining or (len(remaining) == 1 and has_message):
                if not has_message:
                    # Velg språkvariant? Spesifikasjonen gir bokmålsteksten; vi bruker den.
                    p = soup.new_tag("p")
                    # evt. velg nynorsk hvis xml:lang nærmest == nn
                    lang = _nearest_xml_lang(sec) or ""
                    text_nn = "Kapittelbiletet er flytta til neste side."
                    txt = text_nn if lang.startswith("nn") else "Kapittelbildet er flyttet til neste side."
                    p.string = txt
                    pb_before.insert_after(p)
                    inserted_msgs += 1
            else:
                # Det står annet innhold igjen; ikke legg inn “blank side”-melding
                pass

        logger.info("2.3.5.1 - Done. Figures moved: %d, messages inserted: %d", moved, inserted_msgs)

    # 2.3.6 Figures in science books
    # Implemented in 2.3.5

    # 2.3.7 Figures in mathematics books
    """
    2.3.7 Figures in mathematics books
    - Ikke relokér figurer/bilder (håndteres av guards i 2.3.5/2.3.5.1).
    - Ikke trekk ut tekst fra figurer (2.3.2.1), og sørg for at omgivende tekst/struktur
      ikke ligger inne i <figure>:
        * flytt P/UL/OL/DL/TABLE/... + nested FIGURE ut foran <figure>
        * flytt DIV/SPAN med reell tekst/struktur ut
        * pakk løse tekstnoder inn i <p> og plasser foran <figure>
    - Behold <figcaption> og prodnote (<aside epub:type="z3998:production">) inne i <figure>.
    - Idempotent.
    """
    logger.info("2.3.7 - Figures in mathematics books")
    if not args.mathematics:
        logger.info("2.3.7 - Not a mathematics book; skipping.")
    else:
        moved_out = 0
        removed_figtext = 0
        wrapped_text = 0

        for fig in soup.find_all("figure"):
            # 0) Fjern ev. figur-tekstbokser som kan ha slippt gjennom (skal ikke finnes i matte)
            for child in list(fig.find_all("aside", recursive=False)):
                if _is_figure_text_box(child):
                    child.decompose()
                    removed_figtext += 1

            # 1) Flytt uønskede barn ut foran figuren. Samle løse tekster i buffer → <p>.
            text_buf = []

            def flush_text_buf():
                nonlocal wrapped_text, moved_out, text_buf
                if not text_buf:
                    return
                text = "".join(text_buf).strip()
                text_buf.clear()
                if not text:
                    return
                p = soup.new_tag("p")
                p.string = text
                fig.insert_before(p)
                wrapped_text += 1
                moved_out += 1

            for child in list(fig.children):
                # Løse tekstnoder → trekk ut i <p>
                if isinstance(child, NavigableString):
                    if child.strip():
                        text_buf.append(str(child))
                    child.extract()
                    continue

                name = (getattr(child, "name", "") or "").lower()
                if not name:
                    continue

                # Behold bilde/figcaption/prodnote inne i figure
                if _is_image_like(child) or _is_figcaption(child) or _is_prodnote(child):
                    flush_text_buf()
                    continue

                # Flytt åpenbart uønskede blokker
                if name in _BAD_BLOCKS:
                    flush_text_buf()
                    child.extract()
                    fig.insert_before(child)
                    moved_out += 1
                    continue

                # DIV/SPAN med reell tekst eller blokker → flytt ut
                if name in {"div", "span"}:
                    has_text = bool(child.get_text("", strip=True))
                    if has_text or _has_block_descendant(child):
                        flush_text_buf()
                        child.extract()
                        fig.insert_before(child)
                        moved_out += 1
                        continue

                # Andre (sjelden) lar vi stå – spesifikasjonen krever bare at "omgivende tekst"
                # ikke ligger inne i figure. Math/pre/code håndteres ikke her.

            # Flush eventuell oppsamlet løs tekst til slutt
            flush_text_buf()

        logger.info(
            "2.3.7 - Done. moved_out=%d, removed_figtext_boxes=%d, wrapped_text_nodes=%d",
            moved_out, removed_figtext, wrapped_text
        )

    '''
    # 2.3.7.1 Spreadsheets
    if args.mathematics: 
        for figure in soup('figure'): # [:3]: #, attrs={'class':'image'}):
            if figure.find('img'):
                if (table := figure_to_table(nordic.docs, soup, figure)):
                    figure.insert_after(table)
    '''

    """
    2.3.7.1 Spreadsheets
    - Mattebøker: Regneark skal markeres som <table>, ikke som <figure>.
    - Trinn 1 (deterministisk): Hvis <figure> inneholder ekte <table> → løft ut tabell(er), flytt figcaption → <caption>, fjern figure.
    - Trinn 2 (valgfritt): Hvis <figure> kun har bilde som ser ut som regneark og use_llm & table_rpc er gitt:
        kall table_rpc(image_path) og erstatt figuren med returnert <table>. Merk med data-auto-table="spreadsheet".
    - Idempotent: figurer merkes data-table-extracted="true" etter vellykket konvertering.
    """
    logger.info("2.3.7.1 - Spreadsheets → <table> (math only)")

    if not args.mathematics:
        logger.info("2.3.7.1 - Not a mathematics book; skipping.")
    else:
        converted_from_real = 0
        converted_from_img  = 0
        skipped_no_signal   = 0
        failed_rpc          = 0

        for fig in list(soup.find_all("figure")):
            if fig.get("data-table-extracted") == "true":
                continue  # idempotens

            # Finn ev. figcaption-tekst (å bruke som <caption>)
            figcap = fig.find("figcaption", recursive=False)
            figcap_text = _extract_text(figcap) if figcap else ""

            # TRINN 1: figure inneholder ekte tabell?
            if _figure_contains_real_table(fig):
                # Flytt ut alle tabeller i dokumentrekkefølge
                tables = fig.find_all("table")
                if not tables:
                    # kan være fragmenter; da flytter vi hele figure-innholdet, men prøver å finne en table senere
                    pass

                inserted_any = False
                for t in tables:
                    # Fjern t fra figure, og sett på riktig sted (erstatte figure ved første tabell)
                    t.extract()
                    # Sett caption fra figcaption hvis tabellen ikke har caption
                    if _ensure_table_caption_from_figcaption(t, figcap_text):
                        pass
                    # Merk som spreadsheet (kan være nyttig i QA/CSS)
                    classes = set(t.get("class", []) or [])
                    classes.add("spreadsheet")
                    t["class"] = list(classes)
                    t["data-auto-table"] = "spreadsheet"

                    # Første tabell: erstatte figuren
                    if not inserted_any:
                        fig.insert_before(t)
                        inserted_any = True
                    else:
                        # påfølgende tabeller: sett etter forrige tabell
                        prev = t.previous_sibling or t
                        fig.insert_before(t)

                if inserted_any:
                    fig["data-table-extracted"] = "true"
                    fig.decompose()  # “not as <figure>”
                    converted_from_real += 1
                    continue
                # Hvis vi kom hit, fant vi ikke konkrete <table>-noder, fall gjennom til trinn 2

            # TRINN 2: heuristikk for bilde som ser ut som regneark
            imgs = fig.find_all("img", recursive=False)
            if not imgs:
                skipped_no_signal += 1
                continue

            img0 = imgs[0]
            tokens = _tokens_for_img(img0)
            looks_like_spreadsheet = bool(SPREADSHEET_RX.search(tokens))

            if not looks_like_spreadsheet or not (use_llm and callable(table_rpc) and input_base_dir):
                skipped_no_signal += 1
                continue

            img_path = _resolve_image_path(img0.get("src"), input_base_dir)
            if not img_path:
                logger.debug("2.3.7.1 - Could not resolve spreadsheet image path: %s", img0.get("src"))
                skipped_no_signal += 1
                continue

            # RPC: forventer HTML-fragment med <table>… eller None
            try:
                html = table_rpc(img_path)
            except Exception as e:
                logger.warning("2.3.7.1 - table_rpc failed for %s: %s", img_path, e)
                failed_rpc += 1
                continue

            if not html:
                skipped_no_signal += 1
                continue

            # Parse resultatet inn i soup
            frag = BeautifulSoup(html, "lxml")
            new_table = frag.find("table")
            if not new_table:
                skipped_no_signal += 1
                continue

            # Normaliser tabellen: legg på caption fra figcaption hvis mangler
            _ensure_table_caption_from_figcaption(new_table, figcap_text)
            classes = set(new_table.get("class", []) or [])
            classes.add("spreadsheet")
            new_table["class"] = list(classes)
            new_table["data-auto-table"] = "spreadsheet"

            # Sett tabellen der figuren sto og fjern figure
            fig.insert_before(new_table)
            fig["data-table-extracted"] = "true"
            fig.decompose()
            converted_from_img += 1

        logger.info("2.3.7.1 - Done. From real table=%d, From image RPC=%d, Skipped=%d, RPC failed=%d",
                    converted_from_real, converted_from_img, skipped_no_signal, failed_rpc)

    # 2.3.8 Comics, comic strips and graphic novels
    # TODO: Decide format and/or recognize format on source material
    # Possible format:
    #   - https://www.xml.com/pub/a/2001/04/18/comicsml.html
    # Category detection (comics) should be done elsewhere
    """
    2.3.8 Comics, comic strips and graphic novels
    - Identifiser tegneserie-figurer via heuristikk (alt/filnavn/klasser).
    - Sørg for <aside class="prodnote" epub:type="z3998:production">…</aside>.
    - Marker tekst i separate <p>-elementer.
    - Hvis use_llm & comic_text_rpc: hent tekstlinjer og fyll inn (én <p> pr. linje).
    - I mattebøker: ikke trekk ut – behold/lag prodnote med '¤' som plassholder.
    """
    logger.info("2.3.8 - Comics / comic strips / graphic novels")

    processed = 0
    created_aside = 0
    normalized_into_paragraphs = 0
    ocred = 0
    skipped_rpc = 0

    for fig in soup.find_all("figure"):
        imgs = fig.find_all("img", recursive=False)
        if not imgs:
            continue

        # Vurder om dette er tegneserie via tokens
        score = 0
        for im in imgs:
            if COMIC_RX.search(_tokens_for_img(im)):
                score += 1
        if score == 0:
            continue  # ikke tegneserie

        processed += 1

        # Prodnote finnes/skal finnes
        aside, was_created = _find_or_create_prodnote(fig, soup)
        if was_created:
            created_aside += 1

        # Matematikkbok → ikke trekk ut; sørg for '¤' som plassholder
        if args.mathematics:
            txt = (aside.get_text("", strip=True) or "")
            if txt != "¤" or aside.find(["p","em","strong"]):
                aside.clear(); aside.append("¤")
            # merk som comic for idempotens
            aside["data-comic"] = "true"
            continue

        # Hvis det allerede er tekst i asiden, normaliser til <p>-er
        existing_text = aside.get_text("\n", strip=True)
        if existing_text and existing_text != "¤":
            normalized_into_paragraphs += _text_to_paragraphs(aside, soup, existing_text)
            aside["data-comic"] = "true"
            continue

        # Hvis vi kan kjøre OCR/LLM: forsøk å hente tekstlinjer
        if use_llm and callable(comic_text_rpc) and input_base_dir:
            # bruk første bilde som kilde (evt. utvid til alle)
            img_path = _resolve_image_path(imgs[0].get("src"), input_base_dir)
            if not img_path:
                skipped_rpc += 1
            else:
                try:
                    result = comic_text_rpc(img_path)  # kan være List[str] eller str/None
                except Exception as e:
                    logger.warning("2.3.8 - comic_text_rpc failed for %s: %s", img_path, e)
                    result = None
                lines = []
                if isinstance(result, (list, tuple)):
                    lines = [str(x).strip() for x in result if str(x).strip()]
                elif isinstance(result, str) and result.strip():
                    # splitt opp i linjer
                    s = result.replace("\r\n", "\n")
                    lines = [ln.strip() for ln in s.split("\n") if ln.strip()]

                if lines:
                    # fyll inn én <p> per linje
                    for c in list(aside.contents):
                        c.extract()
                    for ln in lines:
                        p = soup.new_tag("p"); p.string = ln
                        aside.append(p)
                    aside["data-ocr"] = "true"
                    aside["data-comic"] = "true"
                    ocred += 1
                    continue
                else:
                    skipped_rpc += 1

        # Ellers: legg inn plassholder hvis helt tom
        if not aside.get_text("", strip=True):
            aside.append("¤")
            aside["data-comic"] = "true"

    logger.info(
        "2.3.8 - Done. processed=%d, created_aside=%d, normalized_to_paragraphs=%d, ocr_added=%d, rpc_skipped=%d",
        processed, created_aside, normalized_into_paragraphs, ocred, skipped_rpc
    )

    # Done BEFORE  2.4.1 Lists that comes after
    """
    2.4.1.1 Lists with missing sequential values
    - Les synlige markører i <li> (før 2.4.1 har strippet dem)
    - Hvis lista hopper i sekvens, sett li[@value] = faktisk ordinal for de elementene
    - Hvis første element starter != 1 pga utelatte elementer, sett value på første <li>
    - Ikke splitt <ol>, ikke bruk start-attributt for dette tilfellet
    - Idempotent: overskriver bare value når den ikke samsvarer
    """
    logger.info("2.4.1.1 - Lists with missing sequential values")

    processed = 0
    adjusted  = 0
    skipped_inconclusive = 0

    for ol in soup.find_all("ol"):
        lis = [li for li in ol.find_all("li", recursive=False)]
        if not lis:
            continue

        # Finn kandidat-markør i hvert li (må finnes i alle; ellers avbryt konservativt)
        markers = []
        series_types = set()
        for li in lis:
            s = _first_text(li)
            if not s:
                markers = []
                break
            m = _WIDE_RX.match(s)
            if not m:
                markers = []
                break
            tok = m.group(1)
            parsed = _parse_marker(tok)
            if not parsed:
                markers = []
                break
            val, typ = parsed
            markers.append((val, typ))
            series_types.add(typ)

        if not markers:
            skipped_inconclusive += 1
            continue

        # Sjekk at alle er samme serie-type (arabisk / a/A / i/I)
        if len(series_types) != 1:
            # blandet (f.eks. a, b, 3) → hopp
            skipped_inconclusive += 1
            continue
        typ = series_types.pop()

        # Finn retning (+1 / -1) ut fra de første to verdiene (ellers +1)
        vals = [v for v, _ in markers]
        if len(vals) >= 2 and vals[1] != vals[0]:
            step = 1 if vals[1] > vals[0] else -1
        else:
            step = 1

        # Sett value på første li hvis start != 1 (utelatte elementer i starten)
        if vals and vals[0] != 1:
            if lis[0].get("value") != str(vals[0]):
                lis[0]["value"] = str(vals[0])
                adjusted += 1

        # Sett value på de li som hopper i sekvens (diff != step)
        expected = vals[0]
        # først li dekkes allerede over; gå fra index 1
        for i in range(1, len(lis)):
            expected += step
            actual = vals[i]
            if actual != expected:
                # hopp oppdaget – sett value=actual
                if lis[i].get("value") != str(actual):
                    lis[i]["value"] = str(actual)
                    adjusted += 1
                # re-synk sekvensforventning til actual (videre hopp vurderes korrekt)
                expected = actual

        processed += 1

    logger.info(
        "2.4.1.1 - Done. processed=%d, adjusted_li_values=%d, skipped_inconclusive=%d",
        processed, adjusted, skipped_inconclusive
    )


    """
    2.4.1.2 Lists with reversed order
    - Oppdag lister som er strikt synkende sekvens (… 5,4,3,2,1 …), basert på:
      1) li[@value] hvis alle har, ellers
      2) synlige markører i <li> (må kjøres før 2.4.1 som stripper markører)
    - Sett <ol reversed>, og start=<første verdi>. Sett type for a/A/i/I.
    - Fjern overflødig type/start hvis tall og start=length uten behov.
    - Idempotent; fjerner reversed hvis lista er økende og reversed var satt (konservativ opprydding).
    """
    logger.info("2.4.1.2 - Lists with reversed order")

    marked_reversed = 0
    unset_reversed  = 0
    skipped         = 0

    for ol in soup.find_all("ol"):
        lis = [li for li in ol.find_all("li", recursive=False)]
        if len(lis) < 2:
            continue

        series = _derive_series_from_values(lis) or _derive_series_from_markers(lis)
        if not series:
            skipped += 1
            continue

        vals = series["values"]
        typ  = series["type"]

        # Sjekk om strikt synkende med steg -1
        is_strict_desc = all(vals[i] == vals[0] - i for i in range(len(vals)))
        is_strict_asc  = all(vals[i] == vals[0] + i for i in range(len(vals)))

        if is_strict_desc:
            # Sett reversed + start = første verdi
            if "reversed" not in ol.attrs:
                ol["reversed"] = ""  # presence attribute
            start_val = vals[0]
            if ol.get("start") != str(start_val):
                ol["start"] = str(start_val)

            # Sett type hvis ikke '1'
            if typ != "1":
                if ol.get("type") != typ:
                    ol["type"] = typ
            else:
                if "type" in ol.attrs:
                    del ol["type"]

            marked_reversed += 1
            continue

        # Ikke synkende → vurder om vi bør fjerne reversed dersom det var satt
        if is_strict_asc and "reversed" in ol.attrs:
            del ol["reversed"]
            # start bør normalt være 1 for økende sekvens
            if "start" in ol.attrs and ol["start"] == "1":
                del ol["start"]
            unset_reversed += 1
            continue

        skipped += 1

    logger.info(
        "2.4.1.2 - Done. set_reversed=%d, unset_reversed=%d, skipped=%d",
        marked_reversed, unset_reversed, skipped
    )

    # 2.4.1 Lists
    """
    2.4.1 Ordered lists <ol>
    - Fjern innskrevet nummerering fra <li>-innhold.
    - Sett riktig type/start/reversed på <ol>.
    - Hopper over lister med <li value=> (de håndteres i 2.4.1.1).
    - Idempotent.
    """
    logger.info("2.4.1 - Ordered lists <ol>")

    processed = 0
    stripped = 0
    skipped_value = 0
    unchanged = 0

    for ol in soup.find_all("ol"):
        lis = [li for li in ol.find_all("li", recursive=False)]
        if not lis:
            continue

        # Hopp over om det finnes value-attrib – 2.4.1.1 tar disse
        if any(li.has_attr("value") for li in lis):
            skipped_value += 1
            continue

        # Ekstra: ikke rør lister som allerede har tydelig innhold først (ikke nummer)
        # Vi forsøker alltid, men validerer konsistens.

        # Hent “første token” i hvert li (før evt punkt/parentes/space)
        tokens = []
        punct_ok = True
        token_matches = []  # lagre matchobjekt for hver li mot en bred regex
        wide_rx = re.compile(rf'^\s*([0-9]+|[A-Za-z]|[ivxlcdmIVXLCDM]+)\s*(?:{_PUNCT_RX}+)?\s+')

        # Finn første tekstsegment i hver li og trekk ut mulig markør
        for li in lis:
            text = li.get_text(" ", strip=True)
            m = wide_rx.match(text)
            if not m:
                punct_ok = False
                break
            tokens.append(m.group(1))
            token_matches.append(m)

        if not punct_ok or not tokens:
            unchanged += 1
            continue

        series = _detect_series(tokens)
        if not series:
            unchanged += 1
            continue

        typ, start_val, is_reversed = series

        # Sett type/start/reversed (idempotent og kun hvis relevant)
        changed_attrs = False
        if typ != "1":
            if ol.get("type") != typ:
                ol["type"] = typ
                changed_attrs = True
        else:
            # fjern evt type hvis satt til noe annet – tall er default
            if "type" in ol.attrs:
                del ol["type"]
                changed_attrs = True

        if is_reversed:
            if "reversed" not in ol.attrs:
                ol["reversed"] = ""  # presence attribute
                changed_attrs = True
            # start skal settes til første markør
            if ol.get("start") != str(start_val):
                ol["start"] = str(start_val)
                changed_attrs = True
        else:
            if "reversed" in ol.attrs:
                del ol["reversed"]
                changed_attrs = True
            # start property kun hvis ikke 1
            if start_val != 1:
                if ol.get("start") != str(start_val):
                    ol["start"] = str(start_val)
                    changed_attrs = True
            else:
                if "start" in ol.attrs:
                    del ol["start"]
                    changed_attrs = True

        # Fjern markøren fra hvert li (kun første forekomst i første tekstnode)
        # Bygg presis regex per li ut fra detektert token (så vi ikke fjerner noe annet)
        for li, tok in zip(lis, tokens):
            li_rx = re.compile(rf'^\s*{re.escape(tok)}\s*(?:{_PUNCT_RX}+)?\s+')
            if _strip_leading_marker(li, li_rx):
                stripped += 1

        processed += 1
        if changed_attrs:
            logger.debug(
                "2.4.1 - <ol id=%r> type=%s start=%s reversed=%s",
                ol.get("id"), ol.get("type"), ol.get("start"), "reversed" in ol.attrs
            )

    logger.info(
        "2.4.1 - Done. processed=%d, stripped_li=%d, skipped_value_lists=%d, unchanged=%d",
        processed, stripped, skipped_value, unchanged
    )



    # 2.4.1.3 List with non-standard numbering
    # This paragraph would already be implemented in the original file

    """
    2.4.1.3 List with non-standard numbering
    - Finn lister hvor de fleste <li> starter med ikke-standard markører (f.eks. 1A, A1, 2.1.3)
    - Sørg for <ol class="list-type-none" style="list-style-type: none;"> slik at markøren
      bevares som tekst i <li>.
    - Konverter <ul> → <ol> når dette oppdages.
    - Rører ikke innholdet i <li>.
    """
    logger.info("2.4.1.3 - List with non-standard numbering")

    processed = 0
    converted_ul = 0
    already_ok = 0

    # Kandidater: både <ol> og <ul> (mange kilder bruker <ul> selv om de viser 1A osv.)
    for lst in soup.find_all(["ol", "ul"]):
        # Hent toppnivå <li> (recursive=False)
        items = lst.find_all("li", recursive=False)
        if len(items) < 2:
            continue

        tokens = [ _first_token(li) for li in items ]
        if not any(tokens):
            continue

        # Klassifiser
        nonstd = sum(1 for t in tokens if _looks_nonstandard_marker(t))
        std    = sum(1 for t in tokens if _looks_standard_marker(t))

        # Heuristikk: ikke-standard hvis minst 60% av punktene har ikke-standard markør
        # (og ikke "overkjørt" av standardmønster).
        if nonstd >= max(2, int(0.6 * len(items))) and nonstd > std:
            # Sørg for <ol>
            if lst.name == "ul":
                # Skånsomt: bytt tag-navn til 'ol' (BS4 tillater dette)
                lst.name = "ol"
                converted_ul += 1

            # Sett list-type none (klasse + style)
            _ensure_listtype_none(lst, logger)

            processed += 1

        else:
            # Hvis allerede har list-type none uten at det egentlig trengs, teller vi som "already_ok"
            if lst.name == "ol" and "list-type-none" in (lst.get("class") or []):
                already_ok += 1

    logger.info("2.4.1.3 - Done. Non-standard lists normalized: %d, ul→ol converted: %d, already_ok: %d",
                processed, converted_ul, already_ok)

    # 2.4.1.4 Jointly given answers in lists
    # Suggested way to solve:
    # If two identical list points are detected,
    # they are put together. TODO: check if this
    # is a good solution.

    """
    2.4.1.4 Jointly given answers in lists (kun mattebøker)
    - Flett LI som begynner med 'og X)'/'samt X)' inn i forrige LI.
    - Korriger videre nummerering med LI@value slik at bokstavene forblir korrekte.
    - Idempotent.
    """
    logger.info("2.4.1.4 - Jointly given answers in lists")
    if not args.mathematics:
        logger.info("2.4.1.4 - Not a mathematics book; skipping.")
    else:
        lists_seen = adjusted_lists = merged_items = valued_set = 0

        # Kandidater: alle <ol type="a"|"A"> i svardeler
        for ol in soup.find_all("ol"):
            t = (ol.get("type") or "")
            if not _ALPHA_TYPE_RX.match(t):
                continue
            if not _in_answer_section(ol):
                continue

            lists_seen += 1
            lis = list(ol.find_all("li", recursive=False))
            if len(lis) < 2:
                continue

            merges_before = 0
            i = 0
            while i < len(lis):
                li = lis[i]
                if i > 0:
                    # finnes 'og c)' i starten av denne LI?
                    letter = _strip_conj_prefix_inplace(li)
                    if letter is not None:
                        # flytt alt innhold fra denne LI inn i forrige LI, prefiksér med "og c) "
                        prev = lis[i - 1]

                        # bygg "og c) " som tekst
                        prefix = NavigableString(f"og {letter})")
                        # legg inn mellomrom om nødvendig
                        _append_with_space(prev, prefix)

                        # flytt alle children (bevar tabeller/markup)
                        for child in list(li.contents):
                            li.contents.remove(child)
                            # legg inn mellomrom mellom prefiks og første faktiske innhold hvis det ikke er tegnsetting
                            if isinstance(child, NavigableString):
                                if not str(child).startswith((" ", "\u00A0", ".", ",", ";", ":")):
                                    prev.append(NavigableString(" "))
                            else:
                                # hvis første innhold er et element, legg en spacing først
                                prev.append(NavigableString(" "))
                            prev.append(child)

                        # fjern LI og oppdater lista
                        li.decompose()
                        lis.pop(i)
                        merges_before += 1
                        merged_items += 1
                        # ikke øk i – vi står nå på elementet som fulgte etter den fjernede
                        continue

                # ingen merge – vurder value-justering etter tidligere merges
                if merges_before > 0:
                    start = _alpha_start(ol)  # default 1
                    expected = start + i      # hva browseren viser (i er 0-basert)
                    desired  = expected + merges_before
                    if desired != expected:
                        li["value"] = str(desired)
                        valued_set += 1
                i += 1

            if merges_before > 0:
                adjusted_lists += 1

        logger.info(
            "2.4.1.4 - Done. Lists seen=%d, lists adjusted=%d, items merged=%d, li@value set=%d",
            lists_seen, adjusted_lists, merged_items, valued_set
        )

    # 2.4.2 Unordered lists <ul>
    """
    2.4.2 Unordered lists <ul>
    - Fjern tekstlige kulemerker i starten av <li>.
    - Normaliser kuleløse lister til class="list-unstyled" (konverter fra inline style/class).
    - Idempotent; rører ikke nav/TOC eller beskyttede blokker.
    """
    logger.info("2.4.2 - Unordered lists <ul>")

    ul_count = 0
    li_cleaned = 0
    ul_plain_normalized = 0

    for ul in soup.find_all("ul"):
        if _in_protected(ul):
            continue
        ul_count += 1

        # 1) Fjern tekstlige kulemerker/dash i starten av hvert <li>
        for li in ul.find_all("li", recursive=False):
            # hopp over beskyttede områder
            if _in_protected(li):
                continue
            changed_now = _strip_text_bullet_prefix_inplace(li)
            changed_now |= _strip_element_bullet_prefix_inplace(li)
            if changed_now:
                li_cleaned += 1

        # 2) Normaliser kuleløse lister → class="list-unstyled"
        if _normalize_plain_ul(ul):
            ul_plain_normalized += 1

    logger.info("2.4.2 - Done. <ul> scanned=%d, <li> cleaned=%d, plain <ul> normalized=%d",
                ul_count, li_cleaned, ul_plain_normalized)

    # 2.4.3 Avoid the use of <p> as children of <li> elements
    """
    2.4.3 Avoid the use of <p> as children of <li> elements
    - Unwrap <p> direkte under <li> når mulig.
    - Hvis flere <p> i samme <li>: sett inn <br> mellom dem.
    - Skip hvis <li> har andre blokkelementer (særlig nested lists).
    - Idempotent.
    """
    logger.info("2.4.3 - Avoid <p> as direct children of <li>")

    scanned = 0
    li_changed = 0
    br_inserted = 0

    for lst in soup.find_all(["ol", "ul"]):
        for li in lst.find_all("li", recursive=False):
            scanned += 1

            # Direkte <p>-barn
            ps = [p for p in li.find_all("p", recursive=False)]
            if not ps:
                continue

            # Skip hvis <li> inneholder andre blokkelementer (nested lists, tabeller, figurer, …)
            if _has_block_children(li):
                continue

            if len(ps) == 1:
                # Kun én <p> → unwrap
                ps[0].unwrap()
                li_changed += 1
                continue

            # Flere <p> → <br> mellom dem og unwrap alle
            for idx, p in enumerate(ps):
                if idx > 0:
                    # Sett inn <br> foran p med mindre det allerede er en <br>
                    prev = _prev_non_ws_sibling(p)
                    if not (getattr(prev, "name", "") == "br"):
                        p.insert_before(soup.new_tag("br"))
                        br_inserted += 1
                p.unwrap()
                li_changed += 1

    logger.info("2.4.3 - Done. <li> scanned=%d, changed=%d, <br> inserted=%d",
                scanned, li_changed, br_inserted)
                
    # 2.4.4 Description Lists
    """
    2.4.4 Description Lists
    - Putt alle <dl> i <aside>.
    - Sett passende klasse (default 'glossary' om ukjent).
    - Legg til heading ved behov, med språkbasert tittel og riktig nivå.
    - Sørg for ': ' på slutten av hver <dt>.
    """
    logger.info("2.4.4 - Description Lists")

    lang = _doc_lang(soup)
    default_title = _GLOSSARY_TITLES.get(lang, _GLOSSARY_TITLES["no"])

    dls = soup.find_all("dl")
    if not dls:
        logger.info("2.4.4 - No <dl> found.")
    else:
        asides_touched = set()
        wrapped = 0
        added_headings = 0
        dt_fixed = 0
        classes_set = 0

        for dl in dls:
            # 1) Sørg for <aside>-wrapper
            aside = None
            for anc in dl.parents:
                if getattr(anc, "name", "").lower() == "aside":
                    aside = anc
                    break

            if not aside:
                aside = soup.new_tag("aside")
                dl.wrap(aside)
                wrapped += 1

            asides_touched.add(aside)

            # 2) Klasse på aside
            classes = set(aside.get("class", []))
            # La eksisterende spesifikke klasser være; ellers gi 'glossary'
            if not classes:
                classes = {"glossary"}
                aside["class"] = list(classes)
                classes_set += 1

            # 3) Sørg for ': ' i dt
            for dt in dl.find_all("dt"):
                if _ensure_dt_colon_space(dt):
                    dt_fixed += 1

        # 4) Overskrifter per aside med <dl> (kun én heading per aside)
        for aside in asides_touched:
            # Finn eksisterende overskrift i denne asiden
            has_heading = False
            for child in aside.find_all(_HEADING_RX, recursive=False):
                has_heading = True
                break

            if not has_heading:
                level = _nearest_heading_level(aside)
                level = min(max(level, 1), 6)
                h = soup.new_tag(f"h{level}")
                h.string = default_title
                # plasser i toppen av asiden
                aside.insert(0, h)
                added_headings += 1

        logger.info(
            "2.4.4 - Done. dl wrapped=%d, aside classes set=%d, headings added=%d, dt fixed=%d",
            wrapped, classes_set, added_headings, dt_fixed
        )

    # 2.4.4.1 Phonetics in description lists
    """
    2.4.4.1 Phonetics in description lists
    - Flytt/normaliser IPA slik at den står i <dt> som '/ipa/' rett før kolon.
    - Fjern IPA fra <dd>.
    - Idempotent og bevarer øvrig markup.
    """
    logger.info("2.4.4.1 - Phonetics in description lists")

    dls = soup.find_all("dl")
    if not dls:
        logger.info("2.4.4.1 - No <dl> found.")

    else:
        moved = 0
        normalized = 0
        already = 0

        for dl in dls:
            for dt, dds in _iter_dt_dd_pairs(dl):
                # Finn IPA i dt og dd
                dt_hit = _first_ipa_in(dt)
                dd_hit = None
                for dd in dds:
                    dd_hit = _first_ipa_in(dd)
                    if dd_hit:
                        break

                # Velg IPA-kilde: prioriter det som allerede er i dt
                ipa_source = None
                src_dd = None
                if dt_hit:
                    ipa_source = dt_hit
                elif dd_hit:
                    ipa_source = dd_hit
                    src_dd = dd

                if not ipa_source:
                    already += 1
                    # Ingen IPA i dette paret – ingenting å gjøre
                    continue

                full, payload = ipa_source
                norm = _normalize_ipa_payload(payload)
                ipa_slash = f"/{norm}/"

                # Hvis dt allerede har samme '/ipa/' → normaliser kun kolon
                if dt_hit:
                    # Er den i klammer? Normaliser til slash
                    if full.startswith("["):
                        # erstatte første forekomst av klammer-varianten i dt med slash-varianten
                        if _remove_first_literal_occurrence(dt, full):
                            normalized += 1
                            # og sett IPA inn riktig ift kolon (i tilfelle den stod feil)
                            _insert_ipa_before_trailing_colon(dt, ipa_slash)
                            _ensure_dt_colon_space_inplace(dt)
                        else:
                            # kunne ikke finne tekstbokstavelig (kan være delt) – bare sikre kolonplassering
                            _insert_ipa_before_trailing_colon(dt, ipa_slash)
                            _ensure_dt_colon_space_inplace(dt)
                    else:
                        # allerede i slash – sørg for korrekt plassering og kolon
                        _insert_ipa_before_trailing_colon(dt, ipa_slash)
                        _ensure_dt_colon_space_inplace(dt)
                    continue

                # Ellers: flytt fra dd → dt
                inserted = _insert_ipa_before_trailing_colon(dt, ipa_slash)
                _ensure_dt_colon_space_inplace(dt)
                if inserted:
                    moved += 1
                    # Fjern IPA-tekst fra dd (bruk original-literal `full`)
                    if src_dd is not None:
                        _remove_first_literal_occurrence(src_dd, full)

        logger.info("2.4.4.1 - Done. Moved=%d, normalized=%d, pairs_without_ipa=%d", moved, normalized, already)

    """
    2.4.4.2 Relocation of description lists
    - Samle <dl> pr. seksjon i én <aside class="glossary" data-relocated="dl-glossary">.
    - Grupper per side med underoverskrift 'Side N' / 'Page N:' og merge dt/dd i ett <dl data-page='N'>.
    - Ikke flytt <dl> som hører eksklusivt til en boks (<aside> med annet innhold enn <dl>).
    - Plasser container: etter (figure/aside), før tasks; ellers på slutten av seksjonen.
    - Idempotent: flytter ikke på nytt og merker containeren.
    """
    logger.info("2.4.4.2 - Relocation of description lists")
    if not args.relocate:
        logger.info("2.4.4.2 - Relocation disabled by flag; skipping.")
    else:
        lang = _doc_lang(soup)

        # Finn alle <dl> som potensielt skal flyttes
        candidates = []
        for dl in soup.find_all("dl"):
            if _dl_in_relocated_container(dl):
                continue  # allerede flyttet
            # Ikke flytt hvis del av en 'boks'-aside med annet innhold
            parent_aside = None
            for anc in dl.parents:
                if getattr(anc, "name", None) == "aside":
                    parent_aside = anc
                    break
            if parent_aside and _is_box_aside(parent_aside):
                continue  # skal forbli i boksen
            candidates.append(dl)

        if not candidates:
            logger.info("2.4.4.2 - No movable <dl> found.")

        moved = 0
        groups_created = 0
        containers_created = 0

        # Flytt per seksjon
        for dl in list(candidates):
            section = _nearest_section(dl, soup) or soup
            container, main_level = _ensure_glossary_container(soup, section, lang)
            if container.get("data-newly-created") != "false" and container.get("data-newly-created") is None:
                containers_created += 1
                container["data-newly-created"] = "false"

            # Finn side
            page = _find_prev_page_number(dl) or "?"
            page_dl = _ensure_page_group(soup, container, page, main_level, lang)
            if page_dl.get("data-newly-created") != "false" and page_dl.get("data-newly-created") is None:
                groups_created += 1
                page_dl["data-newly-created"] = "false"

            # Flytt over dt/dd i korrekt rekkefølge
            items = [child for child in dl.children if isinstance(child, Tag) and child.name in {"dt", "dd"}]
            if items:
                for it in items:
                    page_dl.append(it.extract())
                moved += 1

            # Rydd: ta bort tomme wrappers
            parent = dl.parent
            dl.decompose()

            HEADINGS = {"h1", "h2", "h3", "h4", "h5", "h6"}

            for parent in soup.find_all(class_="glossary"):
                # Finn bare ekte child-tags, ignorer whitespace/tekstnoder
                child_tags = [child for child in parent.children if isinstance(child, Tag)]

                # Tekstinnhold uten whitespace
                text_content = parent.get_text("", strip=True)

                # 1. Fjern helt tomme glossary-elementer
                if not child_tags and not text_content:
                    print("Removing empty glossary:", parent.name, repr(text_content))
                    print(parent)
                    parent.decompose()
                    continue

                # 2. Fjern glossary-elementer der eneste gjenværende child-tag er en overskrift
                if len(child_tags) == 1 and child_tags[0].name in HEADINGS:
                    print("Removing glossary with only heading:", parent.name, repr(text_content))
                    print(parent)
                    parent.decompose()
                    continue


        logger.info("2.4.4.2 - Done. dl moved=%d, containers=%d, page groups=%d",
                    moved, containers_created, groups_created)

    # 2.5 Tasks
    """
    SMR 2.5 Tasks:
    - Merk seksjoner som inneholder oppgaver med class="task".
    - Svarseksjoner merkes class="key" (ikke "task").
    - Overskrifter "Oppgave 1", "Task 2a" → pakkes i individuell <section class="task">.
    - Gruppehoder "Oppgaver/Oppgåver/Tasks" → sørg for at container-seksjonen har class="task".
    """
    logger.info("2.5 - Tasks")

    # Heuristikker / tokens
    TASK_TOKENS   = {"assessment", "exercise", "exercises", "practice", "task", "tasks"}  # epub:type
    ANSWER_TOKENS = {"answer", "answers", "solution", "solutions", "fasit"}               # epub:type
    TASK_HEAD     = {"oppgave", "oppgåve", "task"}       # "Oppgave 1", "Task 2a"
    GROUP_HEAD    = {"oppgaver", "oppgåver", "tasks"}    # gruppehoder

    def _epub_types_method(el):
        et = (el.get("epub::type") or "")
        return {t.strip().lower() for t in re.split(r"[\s;]+", et) if t.strip()}

    def _add_class(el: Tag, klass: str):
        cls = set(el.get("class", []) or [])
        if klass not in cls:
            cls.add(klass)
            el["class"] = list(cls)

    def _is_answer_context(el: Tag) -> bool:
        # Sjekk oppover etter section med epub:type som matcher ANSWER_TOKENS eller class="key"
        for anc in el.parents:
            if getattr(anc, "name", None) == "section":
                if "key" in (anc.get("class") or []):
                    return True
                if _epub_types_method(anc) & ANSWER_TOKENS:
                    return True
        return False

    def _text(el: Tag) -> str:
        return (el.get_text(" ", strip=True) or "").strip()

    def _looks_task_heading(h: Tag) -> bool:
        t = _text(h).lower()
        return any(t.startswith(w + " ") for w in TASK_HEAD)

    def _looks_group_heading(el: Tag) -> bool:
        return _text(el).lower() in GROUP_HEAD
    
    # See above
    '''
    def _first_significant_child(sec: Tag):
        for c in sec.children:
            if isinstance(c, NavigableString):
                if not c.strip():
                    continue
                return c
            if isinstance(c, Tag):
                return c
        return None
    '''

    def _wrap_heading_into_section(h: Tag, klass: str) -> Tag:
        # Hvis heading allerede er første betydningsfulle barn i en section → bare class
        sec = h.find_parent("section")
        if sec and _first_significant_child(sec) is h:
            _add_class(sec, klass)
            return sec

        newsec = soup.new_tag("section")
        _add_class(newsec, klass)

        hid = h.get("id")
        if hid:
            newsec["aria-labelledby"] = hid

        h.insert_before(newsec)
        newsec.append(h.extract())

        # Flytt etterfølgende søsken til neste heading med nivå <=
        lvl = int(h.name[1]) if h.name and h.name[1].isdigit() else 6
        sib = newsec.next_sibling
        while sib is not None:
            nxt = sib.next_sibling
            is_head = isinstance(sib, Tag) and re.fullmatch(r"h[1-6]", sib.name or "", flags=re.I)
            if is_head and int(sib.name[1]) <= lvl:
                break
            newsec.append(sib.extract())
            sib = nxt
        return newsec

    changed = 0

    # (1) Merk eksisterende seksjoner som klart er oppgave- eller svarseksjoner
    for sec in soup.find_all("section"):
        types = _epub_types_method(sec)
        if types & ANSWER_TOKENS:
            _add_class(sec, "key")       # svarseksjon
            changed += 1
        elif types & TASK_TOKENS and not _is_answer_context(sec):
            _add_class(sec, "task")
            changed += 1

    # (2) Individuelle oppgaveoverskrifter → egen <section class="task">
    for h in soup.find_all(re.compile(r"^h[1-6]$", re.I)):
        if _looks_task_heading(h) and not _is_answer_context(h):
            _wrap_heading_into_section(h, "task")
            changed += 1

    # (3) Gruppeoverskrifter “Oppgaver/Oppgåver/Tasks”
    #    – sørg for at containeren er/ligger i en <section class="task">
    for el in soup.find_all(["p"] + [f"h{i}" for i in range(1, 7)]):
        is_bridgehead = el.name == "p" and (el.get("epub:type") or "").lower() == "bridgehead"
        if (is_bridgehead or el.name.startswith("h")) and _looks_group_heading(el) and not _is_answer_context(el):
            sec = el.find_parent("section")
            if sec is None:
                sec = _wrap_heading_into_section(el, "task")
            _add_class(sec, "task")
            changed += 1

    # (4) Fallback: noder med task-aktig epub:type → merk nærmeste section som task (eller pakk)
    for el in soup.find_all(True, attrs={"epub:type": True}):
        if _epub_types_method(el) & TASK_TOKENS and not _is_answer_context(el):
            sec = el.find_parent("section")
            if sec:
                _add_class(sec, "task"); changed += 1
            else:
                wrapper = soup.new_tag("section")
                _add_class(wrapper, "task")
                el.insert_before(wrapper)
                wrapper.append(el.extract())
                changed += 1

    logger.info("2.5 - Tasks: updated %d section(s)", changed)

    # 2.5.1 Specialized task mark-up

    # 2.5.1.1 Main task headings
    """
    2.5.1.1 Main task headings
    - Legg til en hovedoverskrift (“Oppgaver”/“Oppgåver”/“Tasks”) i task-containere som mangler heading.
    - Ikke rør individuelle oppgaver som allerede har egen tittel.
    - Ikke rør fasit/svar (class="key" eller epub:type~answer).
    """
    logger.info("2.5.1.1 - Main task headings")

    lang = _doc_lang(soup)
    title = _task_title_for_lang(lang)

    processed = 0
    added = 0
    skipped_answer = 0
    skipped_singleton = 0
    already_had = 0

    # Kandidater: alle section/artikkel/div som enten er merket .task eller har task-tokens
    candidates = []
    for el in soup.find_all(["section", "article", "div"]):
        cls = set(el.get("class", []) or [])
        et  = _epub_types(el)
        if ("task" in cls) or (et & _TASK_TOKENS):
            candidates.append(el)

    for sec in candidates:
        processed += 1

        # Ikke merk/endre i svar-/fasit-kontekst
        if _is_answer_context(sec) or ("key" in (sec.get("class") or []) or (_epub_types(sec) & _ANSWER_TOKENS)):
            skipped_answer += 1
            continue

        # Har allerede heading? → hopp
        if _has_heading(sec):
            already_had += 1
            continue

        # Er dette sannsynligvis en *individuell oppgave*-seksjon (singleton)?
        # Heuristikk: hvis denne seksjonen ikke inneholder flere task-like direkte barn,
        # men trolig ER selve oppgaven, hopper vi (for å unngå “Oppgaver” foran hver enkelt).
        if _count_immediate_task_children(sec) == 0:
            skipped_singleton += 1
            continue

        # Legg til hovedoverskrift i toppen
        level = _nearest_heading_level(sec)
        h = soup.new_tag(f"h{level}")
        h.string = title
        sec.insert(0, h)
        added += 1

    logger.info(
        "2.5.1.1 - Done. Containers processed=%d, added=%d, already_had=%d, "
        "skipped_singleton=%d, skipped_answer=%d",
        processed, added, already_had, skipped_singleton, skipped_answer
    )
    # 2.5.1.2 Individual task headings
    """
    2.5.1.2 Individual task headings
    - For oppgave-grupper med omfattende/komplisert innhold: gi hver oppgave (<li>) en individuell heading.
    - Språk: nb/no→"Oppgave", nn→"Oppgåve", en→"Task"
    - Nummer: hent fra <ol> (start/value) der det finnes, ellers None for <ul>.
    - Idempotent; konverterer eksisterende "Oppgave 1" i <p> til ekte <hN>.
    """
    logger.info("2.5.1.2 - Individual task headings")

    lang  = _doc_lang(soup)
    label = _task_label_for_lang(lang)

    containers = []
    for el in soup.find_all(["section", "article", "div"]):
        cls = set(el.get("class", []) or [])
        et  = _epub_types(el)
        if ("task" in cls) or (et & _TASK_TOKENS):
            # hopp over svar-kontekst
            if _is_answer_context(el) or ("key" in (el.get("class") or []) or (_epub_types(el) & _ANSWER_TOKENS)):
                continue
            containers.append(el)

    processed_containers = 0
    changed_items = 0

    for cont in containers:
        # finn en toppliste som sannsynligvis representerer "oppgaver i denne gruppen"
        # preferer <ol> (vanligst for nummererte oppgaver)
        top_list = None
        for cand in cont.find_all(["ol", "ul"], recursive=False):
            top_list = cand
            break
        if top_list is None:
            # prøv dypt, men unngå nested lister inni andre <li>
            top_list = cont.find(["ol", "ul"])
        if top_list is None:
            continue

        # heading-nivå for individuelle oppgaver: ett under containerens heading
        level = _nearest_heading_level(cont)

        for li in top_list.find_all("li", recursive=False):
            # kun omfattende/komplekse oppgaver skal få egen heading
            if not _is_complex_li(li):
                continue

            # finn nummer for <ol>, None for <ul>
            number = _compute_decimal_number_for_li(li)

            if _ensure_heading_in_li(soup, li, level, label, number, logger):
                changed_items += 1

        processed_containers += 1

    logger.info(
        "2.5.1.2 - Done. Containers processed=%d, task items updated=%d",
        processed_containers, changed_items
    )

    # 2.5.1.3 Subordinate task headings
    """
    2.5.1.3 Subordinate task headings
    - For oppgaver med underoppgaver (1a, 1b …) og komplekst innhold: gi hver underoppgave en individuell heading.
    - Tekst: 'Oppgave 1a' / 'Oppgåve 1a' / 'Task 1a' (språkstyrt).
    - Nummer hentes fra ytre <ol> (parent-opppgaven). Bokstav hentes fra indre <ol type='a'|'A'> eller heuristisk.
    - Idempotent; konverterer evt. tekstlig heading i første <p>.
    """
    logger.info("2.5.1.3 - Subordinate task headings")
    lang  = _doc_lang(soup)
    label = _task_label_for_lang(lang)

    processed_containers = 0
    updated_subtasks = 0

    # Finn task-containere (som i 2.5.1.2)
    containers = []
    for el in soup.find_all(["section", "article", "div"]):
        cls = set(el.get("class", []) or [])
        et  = _epub_types(el)
        if ("task" in cls) or (et & _TASK_TOKENS):
            if _is_answer_context(el) or ("key" in (el.get("class") or []) or (_epub_types(el) & _ANSWER_TOKENS)):
                continue
            containers.append(el)

    for cont in containers:
        # Toppliste (vanligvis <ol>) direkte i container
        top_list = None
        for cand in cont.find_all(["ol", "ul"], recursive=False):
            top_list = cand
            break
        if top_list is None:
            top_list = cont.find(["ol", "ul"])
        if top_list is None:
            continue

        # Heading-nivå for underoppgaver: ett under container-nivå
        level = _nearest_heading_level(cont)

        # Iterer topp-oppgaver (LI på toppnivå)
        for top_li in top_list.find_all("li", recursive=False):
            # Nummer for topp-oppgave (1,2,3…)
            main_num = _compute_decimal_number_for_li(top_li)

            # Finn *neste nivå* liste(r) inne i toppli (direkte eller første dype)
            sub_list = None
            # helst nested liste som direkte barn
            for cand in top_li.find_all(["ol", "ul"], recursive=False):
                sub_list = cand
                break
            if sub_list is None:
                # prøv dypt, men bare første nested liste
                sub_list = top_li.find(["ol", "ul"])
            if sub_list is None:
                continue

            # For hver underoppgave
            for sub_li in sub_list.find_all("li", recursive=False):
                # Kun omfattende/komplekse underoppgaver trenger heading
                if not _is_complex_li(sub_li):
                    continue

                # Bokstav for underoppgave
                letter = None
                # 1) <ol type='a'|'A'>
                if sub_list.name == "ol":
                    letter = _compute_alpha_letter_for_li(sub_li)
                # 2) <ul> eller Ukjent type → forsøk å lese første token "a)", "b.", "c"
                if letter is None and sub_list.name == "ul":
                    token = (sub_li.get_text(" ", strip=True) or "").split(None, 1)[0]
                    m = re.match(r"([A-Za-z])[.)]?$", token)
                    if m:
                        letter = m.group(1).lower()
                # 3) Fallback: posisjonsbasert a,b,c
                if letter is None:
                    # posisjon i underlista (1→a, 2→b…)
                    idx = 1
                    for sib in sub_list.find_all("li", recursive=False):
                        if sib is sub_li:
                            break
                        idx += 1
                    letter = _alpha_index_to_letters(idx)

                # Bygg heading-tekst
                prefix = label
                if main_num is not None:
                    heading_text = f"{prefix} {main_num}{letter}"
                else:
                    # hvis toppnummer mangler (ul på topp), fall tilbake til bare bokstav
                    heading_text = f"{prefix} {letter}"

                if _ensure_heading_in_li(sub_li, level, heading_text):
                    updated_subtasks += 1

        processed_containers += 1

    logger.info(
        "2.5.1.3 - Done. Containers processed=%d, subordinate tasks updated=%d",
        processed_containers, updated_subtasks
    )

    # 2.5.1.4 Use of section-elements in tasks
    """
    2.5.1.4 Use of section-elements in tasks
    - Oppgaver med individuelle headere → pakk innholdet i <li> inn i <section>.
    - section får class="task" eller class="key" i svar-kontekst.
    - aria-labelledby settes fra oppgave-headingens id.
    - Idempotent; slår sammen/retter eksisterende section-barn og klasser.
    """
    logger.info("2.5.1.4 - Use of <section> elements in tasks")

    changed = 0
    fixed_classes = 0
    merged_existing = 0

    # Finn task-containere (section/article/div med .task eller epub:type∈TASK_TOKENS)
    containers = []
    for el in soup.find_all(["section", "article", "div"]):
        cls = set(el.get("class", []) or [])
        et  = _epub_types(el)
        if ("task" in cls) or (et & _TASK_TOKENS):
            containers.append(el)

    for cont in containers:
        # toppliste på container-nivå (vanligst ol, men ul forekommer)
        top_list = None
        for cand in cont.find_all(["ol", "ul"], recursive=False):
            top_list = cand
            break
        if top_list is None:
            top_list = cont.find(["ol", "ul"])
        if top_list is None:
            continue

        # Gå gjennom oppgave-punkter på topp-nivå
        for li in top_list.find_all("li", recursive=False):
            # Vi krever "individuell heading" (første betydningsfulle barn er <hN>)
            heading = _find_first_heading(li)
            if not heading:
                continue

            # Finn (eller lag) seksjons-wrapper
            direct_sections = [c for c in li.find_all("section", recursive=False)]
            if direct_sections:
                sec = direct_sections[0]
                # Flytt eventuelle søsken inn i sec for å gi tydelig slutt
                moved_any = False
                siblings = [c for c in list(li.children) if c is not sec]
                for c in siblings:
                    # hopp over blanke tekstnoder i enden
                    if isinstance(c, NavigableString) and not c.strip():
                        c.extract()
                        continue
                    sec.append(c.extract())
                    moved_any = True
                if moved_any:
                    merged_existing += 1
            else:
                # Opprett ny section og flytt ALT inn i den
                sec = soup.new_tag("section")
                # Sett inn helt først
                first = li.contents[0] if li.contents else None
                if first is not None:
                    first.insert_before(sec)
                else:
                    li.append(sec)
                # flytt alle barn inn i sec
                for c in list(li.contents):
                    if c is sec:
                        continue
                    sec.append(c.extract())
                changed += 1

            # Sett class basert på kontekst
            if _is_answer_context(sec):
                _drop_class(sec, "task")
                _add_class(sec, "key")
            else:
                _drop_class(sec, "key")
                _add_class(sec, "task")

            # aria-labelledby → heading-id
            _ensure_aria_labelledby(sec, heading)

            fixed_classes += 1

    logger.info("2.5.1.4 - Done. sections_created=%d, sections_merged=%d, classes_set=%d",
                changed, merged_existing, fixed_classes)
        
    # 2.5.1.5 Symbols for task types
    """
    2.5.1.5 Symbols for task types
    - Erstatt sannsynlige symbolske oppgave-ikoner i oppgavekontekst med tekstlig betegnelse.
    - Bevar img-referansen i en HTML-kommentar rett etter.
    - Idempotent; endrer kun når label kan bestemmes sikkert.
    """
    logger.info("2.5.1.5 - Symbols for task types")

    symbol_map = _load_task_symbol_map(folders, logger)
    scanned = replaced = skipped_ctx = skipped_unresolved = 0

    for img in soup.find_all("img"):
        scanned += 1

        if not _in_task_context(img):
            continue  # utenfor oppgave → rør ikke

        if not _is_likely_symbol(img):
            continue  # ser ikke ut som symbol → rør ikke

        if _already_replaced(img):
            continue  # idempotens

        label = _resolve_task_label(img, symbol_map, use_llm, logger)
        if not label:
            skipped_unresolved += 1
            continue

        # Erstatt bildet med tekstlig label og legg inn kommentar
        src = img.get("src") or ""
        alt = img.get("alt") or ""
        comment = Comment(f' symbol: src="{src}" alt="{alt}" ')

        # Sett inn label (ren tekst), med plassering som ikke ødelegger heading/inline
        replacement = NavigableString(label)

        # Bevar litt spacing: hvis neste node er tekst uten innledende space, legg inn én
        needs_space_after = False
        nxt = img.next_sibling
        if isinstance(nxt, NavigableString) and nxt and not str(nxt).startswith((" ", "\u00A0", ".", ",", ";", ":", "!", "?")):
            needs_space_after = True

        img.insert_before(replacement)
        img.insert_after(comment)
        if needs_space_after:
            comment.insert_after(NavigableString(" "))

        img.decompose()
        replaced += 1

    logger.info(
        "2.5.1.5 - Done. img scanned=%d, replaced=%d, unresolved=%d",
        scanned, replaced, skipped_unresolved
    )

    # 2.5.1.6 Match problems
    """
    2.5.1.6 Match problems
    - I containere med epub:type~match-problem: sørg for to separate lister.
    - Konverter tabell (2 kolonner) → to lister (ul list-unstyled).
    - Legg til titler <p><strong>Liste 1</strong></p>, <p><strong>Liste 2</strong></p> (en: List 1/2).
    - Normaliser kuleløse ul → class='list-unstyled'.
    - Idempotent.
    """
    logger.info("2.5.1.6 - Match problems")

    lang = _doc_lang(soup)
    processed = converted = titled = normalized = 0

    # Finn alle match-problem containere
    containers = []
    for el in soup.find_all(True, attrs={"epub:type": True}):
        if _epub_types(el) & _MATCH_TOKENS:
            containers.append(el)

    for cont in containers:
        processed += 1

        # 1) Hvis det finnes <table> → prøv å konvertere
        for tbl in list(cont.find_all("table", recursive=False)) + list(cont.find_all("table")):
            res = _convert_table_to_two_lists(tbl, soup, lang, logger)
            if res:
                converted += 1

        # 2) Finn lister i containeren (vi forventer to), sett titler hvis mangler
        lists = [l for l in cont.find_all(["ol", "ul"], recursive=False)]
        if not lists:
            # prøv litt dypere, men unngå å gå inn i nested <li>
            lists = cont.find_all(["ol", "ul"])
        if lists:
            # typisk to lister – behandle de to første
            for idx, lst in enumerate(lists[:2], start=1):
                if _ensure_list_title_before(lst, _list_title(idx, lang)):
                    titled += 1
                # normaliser ul-plain
                if _normalize_ul_plain(lst):
                    normalized += 1

    logger.info(
        "2.5.1.6 - Done. containers=%d, tables→lists=%d, titles_added=%d, ul_plain_normalized=%d",
        processed, converted, titled, normalized
    )

    # 2.5.1.7 Fill-in-the-blank tasks
    """
    2.5.1.7 Fill-in-the-blank tasks
    - Behold underscores (_) for enkeltbokstav-blanks (uendret).
    - Normaliser ruter/ellipsis/varianter til '....' for ord-blank.
    - Ikke la '....' stå alene i en <p>.
    - Idempotent.
    """
    logger.info("2.5.1.7 - Fill-in-the-blank tasks")

    normalized_nodes = 0
    p_fixed = 0

    # 1) Normaliser tekstnoder i relevant kontekst
    for node in list(soup.find_all(string=True)):
        parent = getattr(node, "parent", None)
        if not parent or not isinstance(parent, Tag):
            continue

        # hopp over uønskede containere
        if parent.name in _SKIP_CONTAINERS:
            continue

        if not _in_fill_task_context(parent):
            continue

        s = str(node)
        # Viktig: ikke rør underscores – de kan være '__' for to bokstaver osv.
        # Vi normaliserer KUN bokser og ellipsis/dot-runs.
        new = _normalize_word_blank(s)

        if new != s:
            try:
                node.replace_with(NavigableString(new))
                normalized_nodes += 1
            except Exception:
                continue

    # 2) Sørg for at '....' ikke står alene i et eget <p>.
    for p in list(soup.find_all("p")):
        if not _in_fill_task_context(p):
            continue
        # Sjekk faktisk strengen i p (inkl. inline)
        txt = p.get_text("", strip=True)
        if _is_only_four_dots(txt):
            _replace_p_four_dots_with_inline(p)
            p_fixed += 1

    logger.info("2.5.1.7 - Done. text_nodes_normalized=%d, standalone_p_four_dots_fixed=%d",
                normalized_nodes, p_fixed)

    # 2.5.1.8 Fill in the correct form – words given
    """
    2.5.1.8 Fill in the correct form – words given
    - Plasser ord i parentes etter setningen (i samme blokk).
    - Flere ord i samme setning → samme parentes, kommaseparert.
    - Har spørsmålet flere blank-setninger og flere ord → tildel ett ord per setning (sekvensielt).
    - Idempotent; fjerner originalt answer-innhold.
    """
    logger.info("2.5.1.8 - Fill in the correct form – words given")

    processed = 0
    updated   = 0
    partial   = 0
    skipped   = 0

    # Finn problem-containere
    candidates = []
    for el in soup.find_all(True, attrs={"epub:type": True}):
        if "fill-in-the-blank-problem" in _epub_types(el):
            candidates.append(el)
    # Fallback: task-kontekst med tydelige blanks men uten eksplisitt type
    if not candidates:
        for el in soup.find_all(["section", "article", "div", "li"]):
            if _in_fill_blank_container(el) and _BLANK_SENTENCE_RX.search(el.get_text("", strip=True) or ""):
                candidates.append(el)

    for cont in candidates:
        processed += 1

        # Finn svarblokk(er) under denne containere
        answers = [a for a in cont.find_all(attrs={"epub:type": True}) if "answer" in _epub_types(a)]
        if not answers:
            skipped += 1
            continue

        # Samle gitt(e) ord
        given_words = []
        for ans in answers:
            given_words.extend(_collect_given_words(ans))

        if not given_words:
            skipped += 1
            continue

        # Finn spørsmålsblokker og “verts-setninger” med blanks
        question_blocks = _find_question_blocks(cont)
        hosts = []
        for qb in question_blocks:
            hosts.extend(_find_blank_hosts(qb))
        # hvis ingen hosts, prøv containeren selv
        if not hosts:
            if _BLANK_SENTENCE_RX.search(cont.get_text("", strip=True) or ""):
                hosts = [cont]
        if not hosts:
            skipped += 1
            continue

        # Fordeling:
        # - ÉN host → ALLE ord i samme parentes
        # - FLERE host og flere ord → ett ord per host i rekkefølge
        # - FLERE host men bare ett ord → legg parentes på første host (logg “partial”)
        if len(hosts) == 1:
            if _append_parens_after(hosts[0], given_words):
                updated += 1
        else:
            if len(given_words) >= len(hosts):
                for host, word in zip(hosts, given_words):
                    if _append_parens_after(host, [word]):
                        updated += 1
                if len(given_words) > len(hosts):
                    partial += 1  # flere ord enn setninger
            else:
                # færre ord enn setninger – sett på første host
                if _append_parens_after(hosts[0], given_words):
                    updated += 1
                partial += 1

        # Fjern/neutraliser answers (så vi ikke får dobbelt visning)
        for ans in answers:
            _neutralize_answer(ans)

    logger.info(
        "2.5.1.8 - Done. containers=%d, updated=%d, partial_mismatches=%d, skipped=%d",
        processed, updated, partial, skipped
    )

    # 2.5.1.9 Tasks which include lines for answers
    """
    2.5.1.9 Tasks which include lines for answers
    - Fjern/ignorer 'linjer' for svar; behold kun spørsmål som lister.
    - Ikke rør fill-in-the-blank (de håndteres i 2.5.1.7).
    - Konverter 2-kolonne tabell (spørsmål | linje) → <ol> med spørsmål.
    - Fjern <hr>/<input>/<textarea>/border-bottom 'linje'-elementer.
    - Fjern/strip <p>/<li> som kun (eller slutt) inneholder linjer.
    """
    logger.info("2.5.1.9 - Tasks which include lines for answers")

    converted_tables = 0
    stripped_blocks  = 0
    removed_lines    = 0

    # 1) Konverter tabeller i relevante oppgavekontekster (ikke fill-in-blank)
    for cont in soup.find_all(True):
        if not isinstance(cont, Tag):
            continue
        if not _in_task_context(cont) or _in_fill_blank_context(cont):
            continue
        for tbl in list(cont.find_all("table")):
            if _convert_2col_table_to_question_list(tbl, soup, logger):
                converted_tables += 1

    # 2) Fjern 'linje'-elementer og strip trailing linjer i blokker
    for node in list(soup.find_all(True)):
        if not isinstance(node, Tag):
            continue
        if not _in_task_context(node) or _in_fill_blank_context(node):
            continue

        # Fjern rene 'linje'-elementer
        if _is_liney_element(node):
            node.decompose(); removed_lines += 1
            continue

        # Strip trailing linjer i <p> og <li>
        if node.name in {"p","li"}:
            if _strip_trailing_lines_in_block(node):
                stripped_blocks += 1
            # Fjern tomme blokker etter stripping
            if not node.find(True) and not (node.get_text("", strip=True) or ""):
                node.decompose()
                removed_lines += 1

    logger.info(
        "2.5.1.9 - Done. tables_converted=%d, blocks_stripped=%d, line_elements_removed=%d",
        converted_tables, stripped_blocks, removed_lines
    )

    # 2.5.1.10 Crossword puzzles
    # TODO: check how crosswords are marked up in original
    """
    2.5.1.10 Crossword puzzles
    - Kryssord skal markeres som BILDE; ledetråder i to <ul class="list-unstyled">.
    - Titler: (en) Down/Across, (andre) Vannrett/Loddrett.
    - Idempotent; konverterer <ol>→<ul>, legger til titler hvis mangler, normaliserer kuleløs <ul>.
    """
    logger.info("2.5.1.10 - Crossword puzzles")

    lang = _doc_lang(soup)
    processed = 0
    ensured_titles = 0
    normalized_uls = 0
    converted_ols = 0
    warned_no_img = 0

    # Finn kryssord-containere
    containers = []
    for el in soup.find_all(True):
        if not isinstance(el, Tag):
            continue
        et = _epub_types(el)
        classes = set(el.get("class", []) or [])
        if (et & _CROSSWORD_TOKENS) or ("crossword" in classes):
            containers.append(el)

    for cont in containers:
        processed += 1

        # 1) Sørg for at kryssordet er bilde
        if not _has_crossword_image(cont):
            # Vi konverterer ikke tabell-rutenett → bilde automatisk (risiko for datatap).
            logger.warning("2.5.1.10 - Crossword container has no <img>; leaving as-is to avoid data loss.")
            warned_no_img += 1

        # 2) Finn inntil to lister for ledetråder (across/down)
        # Vi ser etter lister på første nivå i container; hvis få, prøv dypere.
        lists = [l for l in cont.find_all(["ol", "ul"], recursive=False)]
        if len(lists) < 2:
            lists = cont.find_all(["ol", "ul"])

        # Filtrer ut lister som tydelig ikke er ledetråder (helt tomme etc.)
        lists = [l for l in lists if l.find("li")]

        # Hold på maks to – spesifikasjonen nevner to lister
        lists = lists[:2]

        # Rolle-gjetting
        roles = []
        for lst in lists:
            role = _guess_list_role(lst, lang)
            roles.append(role)

        # 3) Normaliser listetype til <ul> og class='list-unstyled'
        for i, lst in enumerate(lists):
            if lst.name == "ol":
                lists[i] = _ensure_ul_not_ol(lst); converted_ols += 1
        for lst in lists:
            if _normalize_ul_plain(lst):
                normalized_uls += 1
            # hvis fortsatt ikke unstyled, sett den
            cls = set(lst.get("class", []) or [])
            if "list-unstyled" not in cls:
                cls.add("list-unstyled")
                lst["class"] = list(cls)
                normalized_uls += 1

        # 4) Sørg for titler før listene
        if lists:
            # Bestem rekkefølge/titler
            # Prøv å tilordne 'across'/'down' hvis vi klarte å gjette
            title_map = {}
            for lst, role in zip(lists, roles):
                if role == "across":
                    title_map[lst] = _label_across(lang)
                elif role == "down":
                    title_map[lst] = _label_down(lang)

            # For de som ikke fikk rolle, fall tilbake til standardrekkefølge
            leftovers = [lst for lst in lists if lst not in title_map]
            if leftovers:
                # språkspesifikk standardrekkefølge: (en) Down, Across — (andre) Vannrett, Loddrett
                defaults = [_label_down(lang), _label_across(lang)] if lang.startswith("en") else [_label_across(lang), _label_down(lang)]
                for lst, ttl in zip(leftovers, defaults):
                    if lst not in title_map:
                        title_map[lst] = ttl

            # Set/tildel titler
            for lst in lists:
                if _ensure_list_title_before(lst, title_map[lst]):
                    ensured_titles += 1

    logger.info(
        "2.5.1.10 - Done. containers=%d, titles_set=%d, uls_normalized=%d, ols_converted=%d, no_img_warnings=%d",
        processed, ensured_titles, normalized_uls, converted_ols, warned_no_img
    )

    # 2.5.1.11 Tables with one letter in each cell (Word search)
    """
    2.5.1.11 Tables with one letter in each cell (Word search)
    - Fjern tabell, lag én <p> per rad med små bokstaver separert av space.
    - Pakk resultatet i <figure class="word-search">.
    - Bevar ev. caption som <figcaption>.
    - Idempotent.
    """
    logger.info("2.5.1.11 - Word search (tables with one letter per cell)")

    converted = 0
    skipped = 0

    # Hopp over figurer som allerede er word-search
    processed_tables = set()

    for tbl in list(soup.find_all("table")):
        # idempotens: hvis tabellen allerede er konvertert i en tidligere runde, hopp
        if tbl in processed_tables:
            continue

        ok, grid = _table_is_wordsearch(tbl)
        if not ok:
            skipped += 1
            continue

        # Lag figure
        fig = soup.new_tag("figure")
        fig["class"] = (fig.get("class") or []) + ["word-search"]

        # Sett inn figure før tabellen
        tbl.insert_before(fig)

        # Bevar evt. caption -> figcaption
        _ensure_figcaption_copied(tbl, fig)

        # Lag <p> per rad: "a b c d ..."
        for row in grid:
            p = soup.new_tag("p")
            p.append(NavigableString(" ".join(row)))
            fig.append(p)

        # Fjern tabellen
        tbl.decompose()
        converted += 1

    logger.info("2.5.1.11 - Done. converted=%d, skipped=%d", converted, skipped)

    # 2.5.1.12 Tasks with figures
    """
    2.5.1.12 Tasks with figures
    - Figurer som hører til oppgaver skal stå der de står (ikke flyttes).
    - Merk slike figurer og fjern evt. tidligere 'data-relocated-figure'.
    """
    logger.info("2.5.1.12 - Tasks with figures")
    protected = cleaned = 0
    for fig in soup.find_all("figure"):
        if _in_task_or_key_ancestor(fig):
            if fig.get("data-fixed-in-task") != "true":
                fig["data-fixed-in-task"] = "true"
                protected += 1
            if fig.has_attr("data-relocated-figure"):
                del fig["data-relocated-figure"]
                cleaned += 1
    logger.info("2.5.1.12 - Done. Protected=%d, cleaned_relocated_flag=%d", protected, cleaned)

    # 2.5.1.13 Tasks designed as boardgames
    # TODO: check formatting in source
    """
    2.5.1.13 Tasks designed as boardgames
    - Ekstraher tekst fra ruter/bokser og presenter som liste (<ol> eller <ul>).
    - Rekkefølge: tall 1..N > absolutt posisjon (top/left) > tabell rad/kolonne.
    - Behold original figur/bilde. Idempotent – bruker class="boardgame-list".
    """
    logger.info("2.5.1.13 - Tasks designed as boardgames")

    converted = 0
    updated   = 0
    skipped   = 0

    # Finn oppgavekontekster
    tasks = []
    for el in soup.find_all(True):
        if _is_task_container(el):
            tasks.append(el)

    if not tasks:
        logger.info("2.5.1.13 - No task containers found.")
    else:
        for task in tasks:
            # Kandidater: figure/div/section som *ser* ut som brettspill
            candidates = []
            for cand in task.find_all(["figure","div","section"], recursive=True):
                classes = set(cand.get("class", []) or [])
                et = _epub_types(cand)
                if (classes & BOARD_CLASS_HINTS) or ("boardgame" in et) or ("game" in et and "board" in et):
                    candidates.append(cand)
                elif cand.find("table"):
                    ok, _, _ = _extract_table_boxes(cand.find("table"))
                    if ok:
                        candidates.append(cand.find("table"))
                else:
                    ok_abs, _, _ = _extract_abspos_boxes(cand)
                    if ok_abs:
                        candidates.append(cand)

            # Fallback: finnes det en <figure> med mange små “bokser” inni?
            if not candidates:
                for fig in task.find_all("figure"):
                    ok_cls, _, _ = _extract_class_boxes(fig)
                    ok_abs, _, _ = _extract_abspos_boxes(fig)
                    if ok_cls or ok_abs:
                        candidates.append(fig)

            if not candidates:
                skipped += 1
                continue

            for cand in candidates:
                # Sjekk idempotens – har vi allerede skrevet ut en liste like etter?
                existing = _has_generated_board_list(cand)

                # Hent ut bokser
                ok, boxes, meta = False, [], {}
                if cand.name == "table":
                    ok, boxes, meta = _extract_table_boxes(cand)
                else:
                    ok_abs, boxes_abs, meta_abs = _extract_abspos_boxes(cand)
                    if ok_abs:
                        ok, boxes, meta = ok_abs, boxes_abs, meta_abs
                    else:
                        ok_cls, boxes_cls, meta_cls = _extract_class_boxes(cand)
                        if ok_cls:
                            ok, boxes, meta = ok_cls, boxes_cls, meta_cls

                if not ok or not boxes:
                    skipped += 1
                    continue

                # Rekkefølge
                ordered = False
                items_text: list[str] = []

                ok_num, numbered = _ordered_by_leading_number(boxes)
                if ok_num:
                    ordered = True
                    items_text = [txt for (_, txt) in numbered]
                    list_is_ordered = True
                    use_ol = True
                elif meta.get("kind") == "abspos":
                    items_text = _by_abspos(boxes)
                    use_ol = False
                elif meta.get("kind") == "table":
                    items_text = _by_table_rc(boxes)
                    use_ol = False
                else:
                    # siste utvei: behold innsamlet rekkefølge
                    items_text = [b["text"] for b in boxes]
                    use_ol = False

                # Rens tekst litt
                cleaned = []
                for t in items_text:
                    t = re.sub(r"\s+", " ", t).strip()
                    cleaned.append(t)

                # Lag/oppdater liste
                new_list = _mk_list(soup, ordered=use_ol)
                for t in cleaned:
                    li = soup.new_tag("li")
                    li.append(NavigableString(t))
                    new_list.append(li)

                if existing is not None:
                    existing.replace_with(new_list)
                    updated += 1
                else:
                    cand.insert_after(new_list)
                    converted += 1

        logger.info("2.5.1.13 - Done. converted=%d, updated=%d, skipped=%d", converted, updated, skipped)

    # 2.5.1.14 Unformatted lists without bullets within tasks <ul class=”list-unstyled”>
    """
    2.5.1.14 Unformatted lists without bullets within tasks
    - Normaliser eksisterende kuleløse <ul> i oppgaver → class="list-unstyled".
    - Konverter sekvenser av <p> (≥3, inline-only) til <ul class="list-unstyled"> med <li>-elementer.
    - Idempotent: bruker 'generated-unstyled' for å unngå re-konvertering.
    """
    logger.info('2.5.1.14 - Unformatted lists without bullets within tasks')

    tasks = [el for el in soup.find_all(True) if _is_task_container(el)]
    if not tasks:
        logger.info("2.5.1.14 - No task containers found.")
    else:
        normalized_uls = 0
        converted_runs = 0

        for task in tasks:
            # 1) Normaliser eksisterende UL-er
            for ul in task.find_all("ul"):
                if _normalize_unstyled_ul(ul):
                    normalized_uls += 1

            # 2) Finn sekvenser av <p> som bør konverteres til ul.list-unstyled
            #    Vi vurderer bare direkte barn eller flate løp for å unngå å ødelegge struktur.
            children = [c for c in task.children if isinstance(c, (Tag, NavigableString))]
            i = 0
            while i < len(children):
                # hopp whitespace-noder
                if isinstance(children[i], NavigableString) and not children[i].strip():
                    i += 1
                    continue
                # start på <p>-run?
                if isinstance(children[i], Tag) and children[i].name == "p" and _looks_like_list_p(children[i]):
                    run = [children[i]]
                    j = i + 1
                    while j < len(children):
                        c = children[j]
                        if isinstance(c, NavigableString) and not c.strip():
                            j += 1
                            continue
                        if isinstance(c, Tag) and c.name == "p" and _looks_like_list_p(c):
                            run.append(c); j += 1; continue
                        break

                    # Vurder konvertering: minst 3 <p> i run og det finnes ikke allerede en generert liste rett før/etter
                    if len(run) >= 3:
                        # idempotens: sjekk om run allerede er representert av ul.generated-unstyled
                        prev = run[0].previous_sibling
                        while isinstance(prev, NavigableString) and not prev.strip():
                            prev = prev.previous_sibling
                        if isinstance(prev, Tag) and prev.name == "ul" and "generated-unstyled" in (prev.get("class", []) or []):
                            # allerede konvertert tidligere (og flyttet) – hopp
                            i = j
                            continue

                        ul = _mk_ul_unstyled(soup)
                        # Sett inn ul før første p i run
                        run[0].insert_before(ul)

                        # Flytt innholdet fra p til li (bevar inline-innhold)
                        for p in run:
                            li = soup.new_tag("li")
                            # flytt alle p.children til li
                            for node in list(p.contents):
                                li.append(node.extract())
                            ul.append(li)
                            # fjern p
                            p.decompose()

                        converted_runs += 1
                        # Bygg nye children-list og reposition i
                        children = [c for c in task.children if isinstance(c, (Tag, NavigableString))]
                        # sett i til pos etter ul
                        # finn index av ul i children:
                        try:
                            i = children.index(ul) + 1
                        except ValueError:
                            i = j
                        continue
                    else:
                        # kort run – ikke konverter
                        i = j
                        continue
                else:
                    i += 1

        logger.info("2.5.1.14 - Done. normalized_uls=%d, p_runs_converted=%d", normalized_uls, converted_runs)

    # 2.5.1.15 Lists of tasks with non-standard numbering
    """
    2.5.1.15 Lists of tasks with non-standard numbering
    - Inne i oppgaver: oppdag ikke-standard nummerering (1A, 2.10c, A1, ...).
    - Konverter til <ol class="list-type-none" style="list-style-type: none;">.
    - Behold nummer i li-teksten, fjern 'type'/ 'start'/ 'value'.
    """
    logger.info('2.5.1.15 - Lists of tasks with non-standard numbering')

    # Finn alle oppgavecontainere
    tasks = [el for el in soup.find_all(True) if _is_task_container(el)]
    if not tasks:
        logger.info("2.5.1.15 - No task containers found.")
    else:
        converted = 0
        normalized = 0
        skipped = 0

        for task in tasks:
            for lst in task.find_all(["ol", "ul"]):
                # Se kun på toppnivå-listeelementer (ikke rekursivt inn i nested lister)
                lis = lst.find_all("li", recursive=False)
                if not lis:
                    continue
                kinds = [_leading_token_kind(li.get_text(" ", strip=True)) for li in lis]

                # Klassifisering: "nonstd" hvis minst én nonstd og ikke alle er rene std/roman/none
                has_nonstd = any(k == "nonstd" for k in kinds)
                all_std_or_roman = all(k in {"std", "roman"} for k in kinds if k != "none")

                if has_nonstd:
                    # Sørg for <ol> og 'list-type-none'
                    ol = _to_ol(lst, soup)
                    _mark_list_type_none(ol)
                    converted += 1
                else:
                    # Ingen tydelige ikke-standard markører – men dersom UL tydelig starter med tall (std),
                    # lar vi den være. Hvis OL allerede er 'list-type-none', bare normaliser.
                    if lst.name == "ol":
                        # Hvis allerede list-type-none, normaliser stil/attrs
                        cls = set(lst.get("class", []) or [])
                        if "list-type-none" in cls:
                            _mark_list_type_none(lst)
                            normalized += 1
                    else:
                        skipped += 1

        logger.info("2.5.1.15 - Done. converted=%d, normalized=%d, skipped=%d", converted, normalized, skipped)

    # 2.5.1.16 Tasks where examples of answers are given
    """
    2.5.1.16 Tasks where examples of answers are given
    - Finn korte 'eksempelsvar' rett under et spørsmål i samme <li>, flytt inn i parentes på slutten av li.
    - Idempotent: markerer li med data-example-collapsed="true" og sjekker for eksisterende parentes.
    """
    logger.info("2.5.1.16 - Tasks where examples of answers are given")

    tasks = [el for el in soup.find_all(True) if _is_task_container(el) and not _is_answer_section(el)]
    if not tasks:
        logger.info("2.5.1.16 - No task containers (excluding answers) found.")
    else:
        collapsed_count = 0
        skipped_count = 0

        for task in tasks:
            for lst in task.find_all(["ol","ul"]):
                # se på top-level li
                for li in lst.find_all("li", recursive=False):

                    if li.get("data-example-collapsed") == "true":
                        continue  # idempotens

                    # Kandidater for eksempelsvar er typisk direkte barn av li:
                    # <p>/<span>/<em>/<strong>/<div> ... OG små underlister med *1* li
                    candidates: list[Tag] = []
                    for child in li.find_all(recursive=False):
                        nm = getattr(child, "name", "") or ""
                        if nm in {"ol","ul"}:
                            # underliste med nøyaktig ett punkt → kandidat hvis inline-only
                            sublis = child.find_all("li", recursive=False)
                            if len(sublis) == 1 and _is_inline_only(sublis[0]):
                                if _looks_like_example_node(sublis[0]) or _EXAMPLE_PREFIX_RX.match(_text(sublis[0])):
                                    candidates.append(sublis[0])
                            continue
                        if nm in {"p","span","em","strong","i","b","div"} and _is_inline_only(child):
                            if _looks_like_example_node(child) or _EXAMPLE_PREFIX_RX.match(_text(child)):
                                candidates.append(child)

                    # hvis ingen/for mange kandidater → hopp
                    if not candidates:
                        skipped_count += 1
                        continue
                    if len(candidates) > 2 and not use_llm:
                        # vær konservativ uten LLM
                        skipped_count += 1
                        continue

                    # velg én kandidat (første i dokumentrekkefølge; evt. LLM kunne velge bedre)
                    cand = candidates[0]

                    # hent tekst (for <li> kandidat fra underliste, bruk innholdet av den li-en)
                    ctext = _text(cand)
                    ctext = _clean_example_text(ctext)

                    # korte, inline-eksempler: sett grense (f.eks. 160 char) for å hindre store blokker
                    if not ctext or len(ctext) > 160:
                        skipped_count += 1
                        continue

                    # sjekk idempotens (samme parentes finnes)
                    if _li_has_same_parenthetical(li, ctext):
                        # rydde bort kandidatnoden om den er en duplikat-hint
                        try:
                            # om cand er en sub-li inni underliste: fjern hele underlisten hvis den ble tom
                            parent_list = cand.parent if cand.name == "li" else None
                            cand.decompose()
                            if parent_list and isinstance(parent_list, Tag) and parent_list.name in {"ol","ul"}:
                                if not parent_list.find_all("li", recursive=False):
                                    parent_list.decompose()
                        except Exception:
                            pass
                        li["data-example-collapsed"] = "true"
                        collapsed_count += 1
                        continue

                    # finn innsettingspunkt (før første nested liste) eller på slutten
                    anchor = _insertion_anchor_inside_li(li)
                    insert_text = NavigableString(f" ({ctext})")

                    if anchor is not None:
                        anchor.insert_before(insert_text)
                    else:
                        li.append(insert_text)

                    # fjern kandidatnoden fra strukturen
                    try:
                        if cand.name == "li":
                            # underliste med én li → fjern hele listen
                            parent_list = cand.parent
                            cand.decompose()
                            if parent_list and isinstance(parent_list, Tag) and parent_list.name in {"ol","ul"}:
                                if not parent_list.find_all("li", recursive=False):
                                    parent_list.decompose()
                        else:
                            cand.decompose()
                    except Exception:
                        pass

                    li["data-example-collapsed"] = "true"
                    collapsed_count += 1

        logger.info("2.5.1.16 - Done. collapsed=%d, skipped=%d", collapsed_count, skipped_count)

    # 2.5.1.17 Tasks with ticking boxes
    # TODO: Check formatting
    """
    2.5.1.17 Ticking boxes
    - Erstatt tabell-baserte avkryssingsoppsett med <p>H1/H2</p> + <ol>/<ul> av spørsmål.
    - Fjern tabellen (ikke bruk tabeller).
    - Idempotent via .ticking-boxes-head / .ticking-boxes-list.
    """
    logger.info("2.5.1.17 - Tasks with ticking boxes")

    lang = _doc_lang(soup)
    tasks = [el for el in soup.find_all(True) if _is_task_container(el)]
    if not tasks:
        logger.info("2.5.1.17 - No task containers found.")
    else:
        converted = updated = headings_set = skipped = 0

        for task in tasks:
            for tbl in task.find_all("table"):
                ok, headings, statements_from_table, _ = _detect_ticking_table(tbl)
                if not ok:
                    continue

                # 1) Finn/lag liste over spørsmål:
                lst = _existing_ticking_list(tbl)
                if lst is None:
                    # forsøk å konvertere nummererte <p>-run rundt tabellen (typisk layout i eksemplet)
                    p_run = _find_numbered_p_run(tbl)
                    if p_run:
                        lst = _convert_numbered_p_run_to_list(p_run, soup)
                    elif statements_from_table:
                        lst = _make_list_from_statements(soup, statements_from_table, ordered=True)
                        tbl.insert_after(lst)
                    else:
                        skipped += 1
                        continue

                # 2) Sett heading-<p> foran lista
                head_text = _normalize_headings(headings, lang)
                existing_head = _existing_head_p(lst)
                if existing_head is None:
                    head_p = _make_head_p(soup, head_text)
                    lst.insert_before(head_p)
                    headings_set += 1
                else:
                    if _text(existing_head) != head_text:
                        existing_head.string = head_text
                        headings_set += 1

                # 3) Fjern tabellen (spesifikasjonen: do not use tables)
                try:
                    tbl.decompose()
                except Exception:
                    pass

                if "ticking-boxes-list" in (lst.get("class", []) or []):
                    updated += 1  # enten ny eller oppdatert representasjon
                else:
                    converted += 1

        logger.info(
            "2.5.1.17 - Done. converted=%d, updated=%d, headings_set=%d, skipped=%d",
            converted, updated, headings_set, skipped
        )

    # 2.5.1.18 Tasks with tables better represented as lists
    # TODO: make parameter option
    """
    2.5.1.18 Tasks with tables better represented as lists
    - Inne i oppgaver: konverter enkle layout-tabeller til <ul class="list-unstyled table-as-list">.
    - Radene blir <li>, cellene sammenføyes med '; '.
    - Lager valgfri heading-<p class="table-as-list-head"> fra TH-rad (også separert med '; ').
    - Idempotent: erstatter tidligere generert liste med class="table-as-list".
    """
    logger.info("2.5.1.18 - Tasks with tables better represented as lists")

    tasks = [el for el in soup.find_all(True) if _is_task_container(el)]
    if not tasks:
        logger.info("2.5.1.18 - No task containers found.")
    else:
        converted = updated = skipped = 0

        for task in tasks:
            for tbl in task.find_all("table"):
                # hopp hvis tabellen allerede er merket/konvertert
                if tbl.get("data-replaced-as") == "table-as-list":
                    continue

                ok, headers, rows = _is_simple_layout_table(tbl, aggressive=aggressive)
                if not ok:
                    # valgfritt: bruk LLM i edge cases (anbefales av)
                    if use_llm:
                        # her kunne du sendt en liten prompt til LLM via din RabbitMQ-bro
                        # og latt den returnere True/False for “layout-table”
                        pass
                    skipped += 1
                    continue

                existing = _existing_table_as_list(tbl)

                # Bygg utdata
                head_p = _make_head_p(soup, headers) if headers else None
                ul = _make_ul_from_rows(soup, rows)

                if existing is not None:
                    # oppdater eksisterende representasjon
                    # (håndter heading <p> foran lista)
                    prev = existing.previous_sibling
                    while isinstance(prev, NavigableString) and not prev.strip():
                        prev = prev.previous_sibling
                    if head_p:
                        if isinstance(prev, Tag) and prev.name == "p" and "table-as-list-head" in (prev.get("class", []) or []):
                            prev.replace_with(head_p)
                        else:
                            tbl.insert_before(head_p)
                    existing.replace_with(ul)
                    try:
                        tbl.decompose()
                    except Exception:
                        pass
                    updated += 1
                else:
                    # sett inn head + liste der tabellen sto, og fjern tabellen
                    if head_p:
                        tbl.insert_before(head_p)
                    tbl.insert_before(ul)
                    tbl["data-replaced-as"] = "table-as-list"
                    try:
                        tbl.decompose()
                    except Exception:
                        pass
                    converted += 1

        logger.info(
            "2.5.1.18 - Done. converted=%d, updated=%d, skipped=%d",
            converted, updated, skipped
        )

    # 2.5.1.19 Tasks with text between subtasks
    """
    2.5.1.19 Tasks with text between subtasks
    - Flytt mellomtekst til *neste* <li>, i <div class="extra-text"> plassert først i li.
    - Ikke rør første <li>.
    - Behold liste udelte; pakk inn i <p>.
    - Idempotent (hopper over li som allerede starter med .extra-text).
    """
    logger.info("2.5.1.19 - Tasks with text between subtasks")

    tasks = [el for el in soup.find_all(True) if _is_task_container(el)]
    if not tasks:
        logger.info("2.5.1.19 - No task containers found.")
    else:
        moved_blocks = 0
        touched_lists = 0

        for task in tasks:
            for lst in task.find_all(["ol","ul"]):
                lis = lst.find_all("li", recursive=False)
                if len(lis) < 2:
                    continue

                list_touched = False

                # hopp første li; mellomtekst skal aldri legges i første li
                for i in range(1, len(lis)):
                    prev_li, cur_li = lis[i-1], lis[i]

                    # idempotens: dersom cur_li *starter* med .extra-text, hopp
                    first = _first_sig_child(cur_li)
                    if isinstance(first, Tag) and first.name == "div" and "extra-text" in (first.get("class", []) or []):
                        continue

                    between = _collect_between_siblings(lst, prev_li, cur_li)
                    if not between:
                        continue

                    # bygg <div class="extra-text"> med <p>-avsnitt
                    paras = _wrap_into_paragraphs(soup, between)
                    if not paras:
                        continue

                    extra = soup.new_tag("div")
                    extra["class"] = ["extra-text"]
                    for p in paras:
                        extra.append(p)

                    # sett inn *først* i cur_li
                    cur_li.insert(0, extra)
                    moved_blocks += 1
                    list_touched = True

                    # fjern mellomliggende noder (allerede extractet i _wrap_into_paragraphs)
                    # sikre at det ikke ligger igjen blanke tekstnoder
                    cur = prev_li.next_sibling
                    while cur is not None and cur is not cur_li:
                        nxt = cur.next_sibling
                        try:
                            if isinstance(cur, NavigableString) and not cur.strip():
                                cur.extract()
                        except Exception:
                            pass
                        cur = nxt

                if list_touched:
                    touched_lists += 1

        logger.info("2.5.1.19 - Done. moved_blocks=%d, touched_lists=%d", moved_blocks, touched_lists)

    # 2.5.2 Tasks in mathematics books
    """
    2.5.2 Tasks in mathematics books
    - I oppgavekontekst: hver <li> får <section class="task"> + individuell heading.
    - I fasit/svar: <section class="key"> + heading.
    - Heading dannes av listenumre (støtter type/start/value) + ev. trailing stor bokstav (f.eks. 'U').
    """
    logger.info("2.5.2 - Tasks in mathematics books")
    if not getattr(args, "mathematics", False):
        logger.info("2.5.2 - Not a mathematics book; skipping.")
    else:
        wrapped_task = wrapped_key = 0

        # Oppgavecontainere
        for task in soup.find_all(True):
            if not _is_task_container(task):
                continue
            # top-level li i lister
            for lst in task.find_all(["ol","ul"]):
                for li in lst.find_all("li", recursive=False):
                    # bygg label
                    parts = _build_number_path(li)
                    if not parts:
                        # hvis ul uten nummer, hopp (eller lag "•" – men spes sier nummererte oppg.)
                        continue
                    label = ".".join(parts)
                    # ekstra stor bokstav i starten av innhold?
                    extra = _trailing_uc_letter_from_li(li)
                    if extra:
                        label = f"{label} {extra}"

                    sec = _ensure_section_in_li(li, "task", soup)
                    _ensure_heading_in_section(sec, label, soup)
                    wrapped_task += 1

        # Fasit/svarcontainere
        for keysec in soup.find_all(True):
            if not _is_answer_container(keysec):
                continue
            for lst in keysec.find_all(["ol","ul"]):
                for li in lst.find_all("li", recursive=False):
                    parts = _build_number_path(li)
                    label = ".".join(parts) if parts else "Svar"
                    sec = _ensure_section_in_li(li, "key", soup)
                    _ensure_heading_in_section(sec, label, soup)
                    wrapped_key += 1

        logger.info("2.5.2 - Done. wrapped_task=%d, wrapped_key=%d", wrapped_task, wrapped_key)

    # 2.6 Sidebars, text boxes etc.
    """
    2.6 Sidebars, text boxes etc.
    - Normaliser nivå/klasse for reelle sidebokser (<aside>), ev. konverter integrerte til <div>.
    - Idempotent; flytter kun ved behov og respekterer prodnote/fig-desc/glossary.
    """
    logger.info("2.6 - Sidebars, text boxes etc.")

    llm = _ensure_llm_client(logger, use_llm) if use_llm else None

    converted_to_div = lifted = heading_adjusted = framed = 0

    for aside in list(soup.find_all("aside")):
        if _skip_aside(aside):
            continue

        # (Valgfritt) LLM-vurdering: er dette integrert innhold → skal være <div>?
        integral = False
        if use_llm and llm and getattr(llm, "available", False):
            prev_sib = aside.find_previous(lambda t: getattr(t, "name", None) in ("p", "div", "section"))
            next_sib = aside.find_next(lambda t: getattr(t, "name", None) in ("p", "div", "section"))
            resp = llm.classify_aside_integral(
                html_snippet=str(aside)[:2000],
                prev_snip=(prev_sib.get_text(" ", strip=True) if prev_sib else ""),
                next_snip=(next_sib.get_text(" ", strip=True) if next_sib else ""),
            )
            integral = bool((resp or {}).get("integral", False))

        box = aside
        if integral:
            # Konverter til <div> (integrert innhold)
            div = soup.new_tag("div")
            for k, v in list(aside.attrs.items()):
                div.attrs[k] = v
            div.attrs["data-original-tag"] = "aside"
            div.attrs["data-integral"] = "true"
            for n in list(aside.contents):
                div.append(n.extract())
            aside.replace_with(div)
            box = div
            converted_to_div += 1

        # Løft boksen til riktig seksjonsnivå (direkte barn av nærmeste <section>)
        sec = _nearest_section(box, soup)
        top = box
        while top.parent is not None and top.parent is not sec:
            top = top.parent
        if top is not box:
            box.extract()
            top.insert_before(box)
            lifted += 1

        # Juster overskriftsnivå inni boksen (h[x] → riktig nivå)
        h = box.find(_HEADING_RX)
        if h:
            target = f"h{_nearest_heading_level(box)}"
            if h.name != target:
                h.name = target
                heading_adjusted += 1

        # Sørg for ramme-klasser
        _normalize_frame_classes(box)
        framed += 1

    logger.info(
        "2.6 - Done. converted_to_div=%d, lifted=%d, headings_adjusted=%d, framed=%d",
        converted_to_div, lifted, heading_adjusted, framed
    )

    # 2.6.1 Boxes in mathematics books
    logger.info('2.6.1 - Boxes in mathematics books')
    if args.mathematics:
        for aside in soup.find_all('aside'):
            et = (aside.get('epub:type') or '').lower()
            classes = set(aside.get('class', []))
            if et == 'z3998:production' or 'prodnote' in classes or 'fig-desc' in classes:
                continue  # ikke konverter disse
            aside.name = 'div'

    # 2.7 Comments in the margin
    # TODO: find examples and original markup
    """
    2.7 Comments in the margin
    - Identifiser margkommentarer, samle dem i <ul class="margin-comments list-unstyled">
      og plasser på slutten av teksten de tilhører (før tasks/glossary/relokert).
    - Idempotent: fjerner originalboks etter flytting; dedupliserer <li> på tekstinnhold.
    - LLM (valgfritt): binær klassifisering i tvilstilfeller.
    """
    logger.info("2.7 - Comments in the margin")

    # Respekter --no-relocate hvis du bruker det i prosjektet
    if hasattr(args, "relocate") and not getattr(args, "relocate", True):
        logger.info("2.7 - Relocation disabled (--no-relocate); skipping.")
    else:
        # Valgfri LLM-klient
        llm = None
        if use_llm and "._ensure_llm_client" in str(globals().get("_ensure_llm_client", "")):
            try:
                llm = _ensure_llm_client(logger, use_llm)
            except Exception:
                llm = None

        found = moved = 0
        candidates = []

        # Finn potensielle margkommentarer
        for box in soup.find_all(["aside","div"]):
            if not isinstance(box, Tag):
                continue
            if not _looks_like_margin_comment(box):
                continue
            # Hopp over ting som ikke skal behandles her
            if _epub_types(box) & _TASKISH_TOKENS:
                continue
            if "glossary" in (box.get("class", []) or []):
                continue
            candidates.append(box)

        for box in candidates:
            # LLM-avgjørelse i tvilstilfeller (valgfritt)
            if use_llm and llm and getattr(llm, "available", False):
                try:
                    resp = llm.classify_margin_comment(html_snippet=str(box)[:2000])
                    if resp and resp.get("is_margin_comment") is False:
                        continue
                except Exception:
                    pass

            found += 1

            # Finn mål (anker eller seksjon)
            anchor_id = _extract_anchor_id_from_comment(box)
            anchor = soup.find(id=anchor_id) if anchor_id else None

            section = _nearest_section(box, soup) or soup.body
            if section is None:
                logger.debug("2.7 - No <section>/<body> context for margin comment; skipping one.")
                continue

            target = anchor if (anchor and isinstance(anchor, Tag)) else section

            # Finn/lag UL
            ul = _ensure_ul_container(soup, target)

            # Bygg LI og dedupliser
            li = _comment_to_li(soup, box)
            li_txt_key = (li.get_text(" ", strip=True) or "").strip()

            duplicate = False
            if li_txt_key:
                for old in ul.find_all("li", recursive=False):
                    if (old.get_text(" ", strip=True) or "").strip() == li_txt_key:
                        duplicate = True
                        break

            if not duplicate and li_txt_key:
                ul.append(li)
                moved += 1

            # Merk og fjern originalen
            try:
                box["data-processed"] = "margin-comment"
                box.decompose()
            except Exception:
                pass

        logger.info("2.7 - Done. candidates=%d, moved=%d", found, moved)

    # 2.8 Texts with specific styles

    # 2.8.1 Plays and screenplays
    # TODO: find formatting. Make interactive
    """
    § 2.8.1 Plays/screenplays — KJØRES KUN NÅR DU BER OM DET (--plays).
    - Hopper alltid over matematikk- og realfagsbøker.
    - Behandler bare seksjoner med sterke 'play'-cues.
    - Idempotent (rører ikke korrekt eksisterende mark-up).
    """
    logger.info("2.8.1 - Plays and screenplays")

    # Aldri i matte/realfag
    if getattr(args, "mathematics", False) or getattr(args, "science", False):
        logger.info("2.8.1 - Skipping: mathematics/science book.")

    # Kun når skrudd på eksplisitt
    elif not getattr(args, "plays", False):
        logger.info("2.8.1 - Skipping: --plays not set.")

    else:
        # Finn sannsynlige drama-seksjoner
        candidates = [sec for sec in soup.find_all("section") if _section_has_play_cues(sec)]
        if not candidates:
            logger.info("2.8.1 - No convincing play cues found; skipping.")
        else:
            speaker_lines = directions = sections_marked = 0

            for sec in candidates:
                before = set(sec.get("class", []) or [])
                _mark_section_as_play(sec)
                after = set(sec.get("class", []) or [])
                if after != before:
                    sections_marked += 1

                for p in sec.find_all("p"):
                    # hopp over allerede markerte
                    if p.find("span", class_="speaker"):
                        continue
                    if "directions" in (p.get("class", []) or []):
                        continue

                    raw = p.get_text("", strip=False) or ""
                    m = _SPEAKER_RX.match(raw)
                    if m and _valid_speaker_name(m.group(1)):
                        if _wrap_speaker_span_in_p(soup, p, m):
                            speaker_lines += 1
                        continue

                    if _is_entirely_italic_p(p) or _looks_like_stage_direction_text(raw):
                        classes = set(p.get("class", []) or [])
                        if "directions" not in classes:
                            classes.add("directions")
                            p["class"] = sorted(classes)
                            directions += 1

            logger.info("2.8.1 - Done. speaker_lines=%d, directions=%d, sections_marked=%d",
                        speaker_lines, directions, sections_marked)

    # 2.9 Page breaks
    """
    2.9 Page breaks
    - Normaliser alle pagebreaks til <div epub:type="pagebreak" role="doc-pagebreak">.
    - Flytt fra inline/p til blokknivå der mulig (splitter <p> rent).
    - Idempotent; bevarer id/label; lager unik id ved kollisjon.
    """
    logger.info("2.9 - Page breaks")

    # Finn alle potensielle pagebreaks: <span>/<div>/<a>/... med epub:type eller role
    candidates = [el for el in soup.find_all(True) if _is_pagebreak(el)]
    if not candidates:
        logger.info("2.9 - No pagebreaks found.")
    else:
        # For å kunne sikre unike id-er må vi kjenne eksisterende id'er
        existing_ids = set()
        for t in soup.find_all(True):
            _id = t.get("id")
            if _id:
                existing_ids.add(_id)

        converted = moved_p = moved_inline = labeled = 0

        for pb in candidates:
            # Sikre riktig tag/attribs og tomt innhold
            _normalize_pagebreak_tag(pb)
            converted += 1

            # Unik id om nødvendig (bare hvis pb har id)
            pid = pb.get("id")
            if pid:
                new_id = pid
                if pid in existing_ids and soup.find(id=pid) is not pb:
                    new_id = _ensure_unique_id(soup, pid)
                    pb["id"] = new_id
                existing_ids.add(new_id)

            # Sett label fra id hvis mangler
            before_label = _label_from_existing(pb)
            _maybe_set_label_from_id(pb)
            if not before_label and _label_from_existing(pb):
                labeled += 1

            # Flytt ut av <p> først
            if pb.parent and pb.parent.name and pb.parent.name.lower() == "p":
                if _move_pagebreak_out_of_p(soup, pb):  # <— passér soup inn her
                    moved_p += 1
                    continue

            # Hvis parent fortsatt ikke er block → flytt til blokknivå
            if pb.parent and not _is_block(pb.parent):
                _move_pagebreak_to_block_level(pb)
                moved_inline += 1

        logger.info(
            "2.9 - Done. normalized=%d, moved_out_of_p=%d, moved_from_inline=%d, labeled_from_id=%d",
            converted, moved_p, moved_inline, labeled
        )

    # 2.9.1 Relocation of page breaks
    """
    § 2.9.1 Relocation of page breaks
    Forutsetter at § 2.9 har normalisert alle pagebreaks til <div epub:type="pagebreak">.
    Regler:
      • Innen lister: plasser ved slutten av siste <li> på forrige side (aldri først i ny <li>).
      • Ved ny <section>: plasser mellom seksjonsstart og heading, ikke på slutten av forrige seksjon.
      • Inline-sikkerhet: hvis pb ligger i <p>, flytt den ut (bruker § 2.9-hjelper).
    """
    logger.info("2.9.1 - Relocation of page breaks")

    pagebreaks = [el for el in soup.find_all("div") if "pagebreak" in (el.get("epub:type") or "")]
    if not pagebreaks:
        logger.info("2.9.1 - No pagebreaks found.")
    else:
        moved_lists = moved_sections = moved_inline = 0

        for pb in list(pagebreaks):
            # 0) Sikkerhet – hvis pb (fortsatt) ligger i <p>, flytt ut først
            if pb.parent is not None and getattr(pb.parent, "name", "").lower() == "p":
                if _move_pagebreak_out_of_p_safe(soup, pb):
                    moved_inline += 1

            # 1) Liste-regel
            changed = _relocate_pagebreak_in_lists(pb)
            if changed:
                moved_lists += 1
                # Etter flytting: ikke videre regler på denne pb i denne runden
                continue

            # 2) Seksjons-start-regel
            changed = _relocate_pagebreak_at_section_start(soup, pb)
            if changed:
                moved_sections += 1
                continue

            # 3) "Inline til nærmeste punktum" — de facto håndteres av §2.9 ved at pb ikke ligger i <p>.
            #    Hvis du likevel ønsker en heuristikk: hvis pb står rett mellom to <p>,
            #    og forrige <p> ikke slutter på punktum, flytt pb *etter* forrige <p>.
            prev = _prev_sig_sibling(pb)
            nxt  = _next_sig_sibling(pb)
            if isinstance(prev, Tag) and prev.name == "p" and isinstance(nxt, Tag) and nxt.name == "p":
                # hvis forrige <p> ikke ender med setningsslutt, er det ofte mer naturlig at pb kommer etterpå uansett
                endtxt = prev.get_text("", strip=True)
                if endtxt and not re.search(r"[.!?…)]\s*$", endtxt):
                    # la den stå – eller flytt etter prev? Vi velger å la den stå for idempotens/stabilitet.
                    pass

        logger.info(
            "2.9.1 - Done. moved_in_lists=%d, moved_at_section_start=%d, fixed_inline=%d",
            moved_lists, moved_sections, moved_inline
        )

    # 2.10 Tables
    """
    2.10 Tables
    - HTML5-vennlig struktur: <thead>, <tbody>, (ev. <tfoot>).
    - Ledende rader med bare <th> flyttes til <thead>.
    - Resten flyttes til <tbody>.
    - Bevar/sett riktig rekkefølge og 'scope' på <th>.
    """
    logger.info("2.10 - Tables")

    tables = soup.find_all("table")
    if not tables:
        logger.info("2.10 - No tables found.")
    else:
        fixed = created_head = created_body = moved_rows = 0

        for table in tables:
            # Finn eksisterende direkte barn
            caption = table.find("caption", recursive=False)
            thead   = table.find("thead",   recursive=False)
            tbody   = table.find("tbody",   recursive=False)
            tfoot   = table.find("tfoot",   recursive=False)

            # Samle <tr> som ligger *direkte* under <table> (dvs. feil struktur)
            direct_trs = [tr for tr in table.find_all("tr", recursive=False)]

            # Opprett seksjoner ved behov (men append bare hvis de får innhold)
            created_local_head = False
            created_local_body = False
            if thead is None:
                thead = soup.new_tag("thead")
                created_local_head = True
            if tbody is None:
                tbody = soup.new_tag("tbody")
                created_local_body = True

            # Hvis vi har direkte tr-barn: fordel dem til thead/tbody
            header_run = 0
            if direct_trs:
                for tr in direct_trs:
                    if _is_header_row(tr):
                        header_run += 1
                    else:
                        break

                for i, tr in enumerate(direct_trs):
                    tr.extract()
                    if i < header_run:
                        thead.append(tr)
                    else:
                        tbody.append(tr)
                    moved_rows += 1

            # Hvis vi opprettet thead/tbody, men de er tomme, skal de ikke nødvendigvis inn i DOM.
            # Men hvis de har innhold (eller fantes fra før), sørg for riktig rekkefølge.
            def _append_if_needed(node: Tag | None):
                if node and node.parent is None and node.find("tr"):
                    table.append(node)

            # Rydd rekkefølge: caption (om finnes) først, så thead, tbody, tfoot.
            # Ta ut thead/tbody/tfoot og sett inn på nytt i rett rekkefølge.
            # (caption lar vi stå som er, men hvis noen har tuklet rekkefølgen, sørger vi for korrekt.)
            for sec in (thead, tbody, tfoot):
                if sec and sec.parent is table:
                    sec.extract()

            # caption skal være først
            if caption and caption.parent is table:
                caption.extract()
                table.insert(0, caption)

            # Sett inn thead/tbody/tfoot om de har innhold
            _append_if_needed(thead)
            _append_if_needed(tbody)
            if tfoot and tfoot.parent is None:
                table.append(tfoot)

            # Sett scope-attributter for tilgjengelighet
            _assign_scopes(thead if thead.parent is table else None,
                           tbody if tbody.parent is table else None)

            # Statistikk
            if created_local_head and thead.parent is table and thead.find("tr"):
                created_head += 1
            if created_local_body and tbody.parent is table and tbody.find("tr"):
                created_body += 1
            fixed += 1

        logger.info(
            "2.10 - Done. tables=%d, created thead=%d, created tbody=%d, moved rows=%d",
            fixed, created_head, created_body, moved_rows
        )

    # 2.10.1 Table titles
    """
    2.10.1 Table titles
    - Bruk <caption> rett etter <table>.
    - Lag caption fra @title når mulig.
    - Hvis første rad er "enkeltcelle"/kolonnedekkende → bruk innholdet som <caption>, fjern raden.
    - Hvis 'flag cell' (f.eks. én synlig celle + én skjult i første rad) → flytt den synlige cellens innhold til <caption>.
    - Idempotent: flere kjøringer endrer ikke resultatet.
    """
    logger.info("2.10.1 - Table titles")

    tables = soup.find_all("table")
    if not tables:
        logger.info("2.10.1 - No tables found.")
    else:
        used_title = moved_single_row = moved_flag_cell = moved_to_front = 0

        for table in tables:
            # 0) Sanity: hent første <tr> i DOM-rekkefølge (thead/tbody/tfoot spiller ingen rolle)
            first_tr = table.find("tr")

            # 1) Har vi allerede en <caption>? Hvis ikke, prøv 'title'-attributt
            existing_caption = table.find("caption", recursive=False)
            if existing_caption is None:
                tbl_title = table.get("title")
                if tbl_title:
                    cap = _ensure_caption_node(soup, table)
                    if not cap.get_text("", strip=True):
                        cap.clear()
                        cap.append(NavigableString(tbl_title))
                        used_title += 1

            # 2) Hvis fortsatt ingen caption, vurder første rad som “enkeltcelle/colspan”-tittel
            caption = table.find("caption", recursive=False)
            if first_tr is not None and (caption is None or not caption.get_text("", strip=True)):
                cells = first_tr.find_all(["th","td"], recursive=False)
                if cells:
                    # Finn max kolonner blant de neste radene (heuristikk for "spenner over alle kolonner")
                    sibling_rows = []
                    cur = first_tr.find_next_sibling()
                    while cur is not None and getattr(cur, "name", None) is not None:
                        if cur.name == "tr":
                            sibling_rows.append(cur)
                            if len(sibling_rows) >= 5:
                                break
                        cur = cur.find_next_sibling()
                    # hvis ingen søsken, test bare mot antall celler i første rad (>=1 gir håndtering)
                    max_cols = 0
                    for tr in sibling_rows:
                        max_cols = max(max_cols, _row_effective_cols(tr))
                    if max_cols == 0:
                        # hvis vi ikke fant andre rader, men første rad har 1 celle — regn som tittelrad
                        max_cols = max(max_cols, 2)  # tving “flere kolonner”-antakelse

                    first_cols = _row_effective_cols(first_tr)
                    # kandidat: nøyaktig én celle (evt. colspan) OG (effektive kolonner >= 1) og max_cols >= 2
                    if first_cols >= 1 and (len(cells) == 1 or first_cols >= max_cols):
                        # flytt innhold fra cellen til <caption> og fjern raden
                        cap = _ensure_caption_node(soup, table)
                        if not cap.get_text("", strip=True):
                            cap.clear()
                            # flytt innhold (bevar inline mark-up)
                            for n in list(cells[0].contents):
                                cap.append(n.extract())
                            moved_single_row += 1
                        # fjern hele raden
                        first_tr.decompose()
                        # oppdatér peker (ikke brukt videre)
                        first_tr = table.find("tr")

            # 3) “Flag cell” i øverste venstre hjørne (f.eks. to celler i første rad hvor én er skjult)
            # Heuristikk: første rad har 1–2 celler og nøyaktig én 'synlig' celle med faktisk tekst.
            caption = table.find("caption", recursive=False)
            if first_tr is not None and (caption is None or not caption.get_text("", strip=True)):
                cells = first_tr.find_all(["th","td"], recursive=False)
                if 1 <= len(cells) <= 2:
                    visible = [c for c in cells if not _is_collapsed(c)]
                    if len(visible) == 1:
                        txt = visible[0].get_text("", strip=True)
                        if txt:
                            cap = _ensure_caption_node(soup, table)
                            if not cap.get_text("", strip=True):
                                cap.clear()
                                for n in list(visible[0].contents):
                                    cap.append(n.extract())
                                moved_flag_cell += 1
                            # hvis raden nå er "tømt" eller bare inneholder kollapset celle → fjern den
                            rest_cells = [c for c in first_tr.find_all(["th","td"], recursive=False)]
                            if not rest_cells or all(_is_collapsed(c) or not c.get_text("", strip=True) for c in rest_cells):
                                first_tr.decompose()

            # 4) Sørg for at <caption> er første direkte barn av <table>
            before = table.find("caption", recursive=False)
            if before is not None and before.previous_sibling is not None:
                _move_caption_first(table)
                moved_to_front += 1

        logger.info(
            "2.10.1 - Done. from @title=%d, single-row→caption=%d, flag-cell→caption=%d, moved-to-front=%d",
            used_title, moved_single_row, moved_flag_cell, moved_to_front
        )

    # 2.10.2 Tables without clear boundaries between rows or columns
    # This does not apply in electronic books
    """
    2.10.2 Tables without clear boundaries
    - Lint: finn celler som sannsynligvis inneholder flere elementer.
    - Valgfri normalisering (--table-normalize-cell-lists):
      konverter til <ul class="list-unstyled"> inne i cellen (ikke endre rader/kolonner).
    - Hvis --llm: bruk modellen for å bekrefte normalisering ved tvilstilfeller.
    """
    logger.info("2.10.2 - Tables without clear boundaries between rows/columns")

    llm = None
    if getattr(args, "llm", False):
        try:
            llm = _ensure_llm_client(logger, args.llm)  # din eksisterende stub
        except Exception:
            llm = None

    tables = soup.find_all("table")
    if not tables:
        logger.info("2.10.2 - No tables found.")
    else:
        flagged = normalized = 0

        for table in tables:
            for tr in table.find_all("tr"):
                for cell in tr.find_all(["td", "th"], recursive=False):
                    if not _is_suspicious_cell(cell):
                        continue

                    flagged += 1
                    cell["data-table-lint"] = "suspicious-multiitem"

                    do_normalize = bool(getattr(args, "table_normalize_cell_lists", False))
                    # aldri auto-normaliser <th> (bevar overskrifter), men logg
                    if cell.name == "th":
                        do_normalize = False

                    # Hvis LLM er aktiv: spør modellen ved tvil (kun hvis do_normalize er True)
                    if do_normalize and llm and getattr(llm, "available", False):
                        snippet = cell.get_text(" ", strip=True)[:400]
                        resp = llm.classify_cell_multiitem(snippet=snippet)
                        # forventet { "multiitem": bool, "confidence": float }
                        if not resp or not resp.get("multiitem", False) or resp.get("confidence", 0) < 0.66:
                            do_normalize = False

                    if do_normalize:
                        changed = _normalize_cell_to_ul(cell, soup, logger)
                        if changed:
                            normalized += 1

        logger.info("2.10.2 - Done. Flagged cells=%d, Normalized=%d", flagged, normalized)

    # 2.10.3 Avoid use of <em> or <strong> in <th>
    logger.info('2.10.3 - Avoid use of <em> or <strong> in <th>')

    unwrapped = 0
    for th in soup.find_all("th"):
        # Finn alle em/strong (rekursivt) inne i th og fjern selve taggen, behold innholdet
        for emph in list(th.find_all(["em", "strong"])):
            emph.unwrap()
            unwrapped += 1

    logger.info(f'2.10.3 - Unwrapped {unwrapped} <em>/<strong> tag(s) inside <th>.')

    # 2.10.4 Avoid use of <p> within table cells
    logger.info('2.10.4 - Avoid use of <p> within table cells')


    unwrapped_single = merged_multi = skipped = 0

    for cell in soup.find_all(["td", "th"]):
        # hopp celler med tydelig matematikk
        if _has_math_content(cell):
            skipped += 1
            continue

        ps = _cell_direct_ps(cell)
        if not ps:
            continue

        # Hvis cellen inneholder andre blokker i tillegg til p (lister, figurer, tabeller, osv.),
        # la stå – her er <p> ofte nødvendig for struktur/lesbarhet
        other_blocks = [c for c in cell.children
                        if getattr(c, "name", None) and c.name in _BLOCK_TAGS and c.name != "p"]
        if other_blocks:
            skipped += 1
            continue

        # 1) Én enkel <p> som eneste innhold -> unwrap hvis trygg
        non_ws_children = [c for c in cell.children if not (isinstance(c, str) and not c.strip())]
        if len(ps) == 1 and len(non_ws_children) == 1:
            p = ps[0]
            if not _p_has_significant_attrs(p) and not _has_block_descendants(p):
                # flytt innhold ut og fjern p
                for n in list(p.contents):
                    p.insert_before(n.extract())
                p.decompose()
                unwrapped_single += 1
            else:
                skipped += 1
            continue

        # 2) Flere <p> i samme celle, og cellen har ikke andre blokkelementer -> slå sammen med <br>
        # Bevar inline-formattering ved å flytte innholdet ut og legge inn <br> mellom.
        if len(ps) >= 2:
            # unngå å lage gigantiske br-vegger; gjør det kun dersom p-ene er "enkle"
            if any(_has_block_descendants(p) for p in ps):
                skipped += 1
                continue
            # Gjennomfør merge
            for i, p in enumerate(ps):
                # flytt innholdet til cellen
                for n in list(p.contents):
                    p.insert_before(n.extract())
                # legg inn <br> mellom avsnitt (ikke etter siste)
                if i < len(ps) - 1:
                    p.insert_before(soup.new_tag("br"))
                p.decompose()
            _collapse_consecutive_br(cell)
            merged_multi += 1
            continue

        # 3) Default: la stå
        skipped += 1

    logger.info(f"2.10.4 - Done. Unwrapped single <p>: {unwrapped_single}, merged multi-<p>: {merged_multi}, skipped: {skipped}")

    # 2.10.5 Lists within tables
    # Already implemented by SMR 2.4
    stats = {"li_p_unwrapped":0, "li_p_merged":0, "bullets_stripped":0, "ul_plain_set":0, "ol_plain_nonstd":0, "skipped_math_cell":0}

    for cell in soup.find_all(["td","th"]):
        # hopp matte-celler
        if _has_math(cell):
            stats["skipped_math_cell"] += 1
            continue

        # Finn lister direkte inne i cellen (eller dypere – lister kan ligge et nivå ned)
        for lst in cell.find_all(["ul","ol"]):
            # 2.4.3: P i LI
            for li in lst.find_all("li", recursive=False):
                if _unwrap_single_p_if_simple(li):
                    stats["li_p_unwrapped"] += 1
                elif _merge_multi_p_with_br(li, soup):
                    stats["li_p_merged"] += 1

            # 2.4.2: Kuletegn i UL
            if lst.name == "ul":
                any_stripped = False
                for li in lst.find_all("li", recursive=False):
                    if _strip_leading_bullet_in_li(li):
                        any_stripped = True
                        stats["bullets_stripped"] += 1
                # Sett list-unstyled når listen ikke har synlige kuler/dash
                if _ul_needs_plain_class(lst):
                    _ensure_class(lst.attrs, "list-unstyled")
                    stats["ul_plain_set"] += 1

            # 2.4.1.3: Ikke-standard OL → plain
            if lst.name == "ol" and _mark_ol_nonstandard(lst):
                _ensure_class(lst.attrs, "list-type-none")
                _ensure_style_none(lst)
                stats["ol_plain_nonstd"] += 1


    logger.info(
        "2.10.5 - Done. Unwrapped LI<p>=%d, merged LI<p>=%d, bullets stripped=%d, ul plain set=%d, ol nonstd plain=%d, math cells skipped=%d",
        stats["li_p_unwrapped"], stats["li_p_merged"], stats["bullets_stripped"], stats["ul_plain_set"],
        stats["ol_plain_nonstd"], stats["skipped_math_cell"]
    )

    # 2.10.6 Tables where all table cells are empty
    converted = 0
    skipped_not_empty = 0
    skipped_no_headings = 0

    for table in list(soup.find_all("table")):
        # Idempotens: hopp over hvis allerede prosessert
        if table.get("data-processed-empty") == "true":
            continue

        tds = table.find_all("td")
        if not tds:
            # Ingen <td> → dette kravet gjelder ikke eksplisitt (kan være ren header-tabell)
            continue

        # Alle `td` må være tomme
        if not all(_cell_is_empty(td) for td in tds):
            skipped_not_empty += 1
            continue

        # Finn header-rad for å kunne hoppe over den når vi henter radoreskrifter
        header_cells = _header_row_cells(table)
        header_row = header_cells[0].parent if header_cells else None

        cols = _col_headings(table)
        rows = _row_headings(table, header_row=header_row)

        if not cols and not rows:
            # Uten kolonne-/radoreskrifter gir det lite mening å erstatte med lister
            skipped_no_headings += 1
            continue

        # Bygg figure
        fig = soup.new_tag("figure")
        fig["class"] = ["empty-table-headings"]
        if table.get("id"):
            fig["data-from-table-id"] = table["id"]

        cap_text = _extract_caption_text(table)
        if cap_text:
            fc = soup.new_tag("figcaption")
            fc.string = cap_text
            fig.append(fc)

        ul_cols = _mk_ul_items(soup, cols, "col-headings")
        ul_rows = _mk_ul_items(soup, rows, "row-headings")
        if ul_cols: fig.append(ul_cols)
        if ul_rows: fig.append(ul_rows)

        table.insert_before(fig)
        table["data-processed-empty"] = "true"
        table.decompose()
        converted += 1

    logger.info(
        "2.10.6 - Done. Converted tables: %d, skipped (not all cells empty): %d, skipped (no headings found): %d",
        converted, skipped_not_empty, skipped_no_headings
    )

    # 2.10.7 Do not use tables purely as a formatting tool
    # TODO: The conversion of table to list should be done interactively

    try:
        llm = _ensure_llm_client(logger, getattr(args, "llm", False)) if getattr(args, "llm", False) else None
    except NameError:
        llm = None  # _ensure_llm_client finnes ikke i dette miljøet

    converted, skipped_complex, skipped_heur, skipped_llm = 0, 0, 0, 0
    created_uls = []

    for table in list(soup.find_all("table")):
        # Idempotens
        if table.get("data-processed-table-as-list") == "true":
            continue
        if _has_complex_content(table):
            skipped_complex += 1
            continue

        is_layout, reason = _estimate_layout_table(table)
        if not is_layout and llm:
            llm_decision = _llm_agrees_layout(table, llm, logger)
            if llm_decision is False:
                skipped_llm += 1
                continue
            if llm_decision is True:
                is_layout = True

        if not is_layout:
            skipped_heur += 1
            continue

        cap = _caption_text(table)
        header_exists = bool(_has_any_header(table))
        ul = _make_ul_from_table(table, soup, use_headers=header_exists)
        if not ul:
            skipped_heur += 1
            continue

        # Sett inn caption som <p> foran lista
        if cap:
            pcap = soup.new_tag("p")
            pcap["class"] = ["table-caption"]
            pcap.string = cap
            table.insert_before(pcap)

        table.insert_before(ul)
        created_uls.append(ul)

        table["data-processed-table-as-list"] = "true"
        table.decompose()
        converted += 1

    logger.info(
        "2.10.7 - Done. Converted=%d, skipped_complex=%d, skipped_heuristics=%d, skipped_llm=%d",
        converted, skipped_complex, skipped_heur, skipped_llm
    )

    # --- Lett etter-validering (logger kun) -------------------------------------
    bad_semicolons = 0
    bad_header_pairs = 0

    for ul in created_uls:
        for li in ul.find_all("li", recursive=False):
            t = re.sub(r"\s+", " ", (li.get_text(" ", strip=True) or ""))
            if re.search(r";\s*;", t):
                bad_semicolons += 1
            # “Header: ” uten verdi (slutter rett etter kolon eller før semikolon/slutt)
            if re.search(r":[\s]*(;|$)", t):
                bad_header_pairs += 1

    if bad_semicolons or bad_header_pairs:
        logger.warning(
            "2.10.7 - Post-check: double-separators=%d, header-without-value=%d",
            bad_semicolons, bad_header_pairs
        )

    # 2.10.8 Spreadsheets as tables
    # DEPRECATED
    # This requirement should be covered by SMR 2.3.7.1

    # 2.11 Quotations, blockquotes, sources
    llm = _ensure_llm(logger, args)
    moved_bq = moved_fig = moved_tbl = 0
    skipped = 0

    # 1) Blockquotes: flytt kilde inn i blockquote
    for bq in soup.find_all("blockquote"):
        if _should_skip_target(bq) or bq.find("cite"):
            continue
        sib = _next_meaningful_sibling(bq)
        if not sib or not getattr(sib, "name", None):
            continue

        move_it = _is_source_like_tag(sib)
        if not move_it and llm:
            move_it = bool(_llm_says_source(llm, str(bq), _node_text(sib)))

        if move_it:
            _append_cite_to_blockquote(bq, soup, sib)
            moved_bq += 1

    # 2) Figures: flytt kilde inn i figcaption
    for fig in soup.find_all("figure"):
        if _should_skip_target(fig):
            continue
        # Hvis figcaption allerede har <cite>, anta OK
        fc = fig.find("figcaption")
        if fc and fc.find("cite"):
            continue

        sib = _next_meaningful_sibling(fig)
        if not sib or not getattr(sib, "name", None):
            continue

        move_it = _is_source_like_tag(sib)
        if not move_it and llm:
            move_it = bool(_llm_says_source(llm, str(fig), _node_text(sib)))

        if move_it:
            _append_cite_to_figcaption(fig, soup, sib)
            moved_fig += 1

    # 3) Tabeller: flytt kilde inn i caption
    for tbl in soup.find_all("table"):
        if _should_skip_target(tbl):
            continue
        cap = tbl.find("caption")
        if cap and cap.find("cite"):
            continue

        sib = _next_meaningful_sibling(tbl)
        if not sib or not getattr(sib, "name", None):
            continue

        move_it = _is_source_like_tag(sib)
        if not move_it and llm:
            move_it = bool(_llm_says_source(llm, str(tbl), _node_text(sib)))

        if move_it:
            _append_source_to_caption(tbl, soup, sib)
            moved_tbl += 1

    logger.info(
        "2.11 - Done. Moved: blockquotes=%d, figures=%d, tables=%d",
        moved_bq, moved_fig, moved_tbl
    )

    # 2.12 Footnotes and endnotes

    # 2.12.1 Footnotes
    llm = _ensure_llm(logger, args)
    moved_single = moved_lists = 0
    skipped = 0

    # Samle kandidater i dokumentrekkefølge (før vi muterer)
    candidates: list[Tag] = []
    for el in soup.find_all(True):
        if _is_footnote_like(el):
            candidates.append(el)

    # Idempotens: ikke ta de som allerede er merket
    candidates = [el for el in candidates if el.get("data-relocated-footnote") != "true"]

    # Flytt liste-containere først (for å bevare nummerering), deretter enkelt-noter
    list_candidates, single_candidates = [], []
    for el in candidates:
        cont = _belongs_to_footnote_list(el)
        if cont is not None:
            # flytt containeren (ikke den enkelte li)
            list_candidates.append(cont)
        else:
            single_candidates.append(el)

    # Dedupliser containere (kan forekomme samme flere ganger via ulike <li>)
    seen = set()
    uniq_list_containers = []
    for c in list_candidates:
        key = id(c)
        if key not in seen:
            uniq_list_containers.append(c)
            seen.add(key)

    # 1) Flytt fotnote-lister (ol/ul) til slutten av seksjonen
    for cont in uniq_list_containers:
        # Finn relevant seksjon
        sec = _nearest_section(cont, soup)
        if not sec:
            skipped += 1
            continue
        # Sjekk om containeren allerede ligger sist
        if cont.parent is sec and _at_end_of_section(sec, cont):
            cont["data-relocated-footnote"] = "true"
            continue

        # LLM (valgfritt) dersom containeren ikke tydelig er fotnoter
        if not (_class_tokens(cont) & {"footnotes"}) and not (_etokens(cont) & {"footnotes","endnotes"}) and _role_token(cont) not in {"doc-footnotes","doc-endnotes"}:
            if llm:
                decision = _llm_is_footnote(llm, str(sec), _node_text(cont))
                if decision is False:
                    skipped += 1
                    continue

        # Flytt
        cont.extract()
        sec.append(cont)
        cont["data-relocated-footnote"] = "true"
        moved_lists += 1

    # 2) Flytt enkeltstående fotnoter til slutten av seksjonen (men etter evt. fotnote-liste)
    for fn in single_candidates:
        # Hvis noden rakk å bli fjernet (f.eks. via listeflytt), hopp
        if not getattr(fn, "parent", None):
            continue

        sec = _nearest_section(fn, soup)
        if not sec:
            skipped += 1
            continue

        # Finn om det allerede finnes en fotnote-liste på slutten – i så fall legg etter lista
        kids = _significant_children(sec)
        insert_after = None
        for k in reversed(kids):
            if getattr(k, "name", None) in {"ol","ul"}:
                pcl = {c.lower() for c in _class_tokens(k)}
                if "footnotes" in pcl or _role_token(k) in {"doc-endnotes","doc-footnotes"} or (_etokens(k) & {"footnotes","endnotes"}):
                    insert_after = k
                    break

        # Idempotens: hvis fn allerede ligger sist og/eller etter fotnotelista, hopp
        if fn.parent is sec and _at_end_of_section(sec, fn):
            fn["data-relocated-footnote"] = "true"
            continue

        # Dersom vi skal legge etter en eksisterende liste, og fn er en <li> fra et annet sted:
        if insert_after is not None and fn.name == "li":
            # Legg den inn i samme liste om det gir mening
            insert_after.append(fn.extract())
            fn["data-relocated-footnote"] = "true"
            moved_single += 1
            continue

        # LLM (valgfritt) om heuristikk er tvilsom
        if not _is_footnote_like(fn):
            if llm:
                decision = _llm_is_footnote(llm, str(sec), _node_text(fn))
                if decision is False:
                    skipped += 1
                    continue

        # Flytt fn til slutten (eller etter lista)
        fn.extract()
        if insert_after is not None and insert_after.parent is sec:
            insert_after.insert_after(fn)
        else:
            sec.append(fn)
        fn["data-relocated-footnote"] = "true"
        moved_single += 1

    logger.info("2.12.1 - Done. Moved lists=%d, moved singles=%d, skipped=%d",
                moved_lists, moved_single, skipped)

    # 2.12.2 Endnotes and chapter notes
    containers: list[Tag] = []
    singles: list[Tag] = []
    for el in soup.find_all(True):
        if _end_is_endnotes_container(el):
            containers.append(el)
        elif _end_is_single_endnote(el):
            singles.append(el)

    # Hvis ingen eksplisitte containere, se etter sannsynlige (heading 'Noter', 'Endnotes' etc.)
    llm = _end_ensure_llm(logger, args)
    if not containers:
        # Heuristisk: <section>/<div> med heading-tekst "Noter"/"Endnotes"/"Kapittelnoter"
        for cand in soup.find_all(["section","div"]):
            if getattr(cand, "name", None) and cand.get("data-relocated-endnotes") != "true":
                # Sjekk etter heading
                h = cand.find(re.compile(r"^h[1-6]$", re.I))
                title = (h.get_text(" ", strip=True).lower() if h else "").strip()
                if title in {"noter", "sluttnoter", "kapittelnoter", "endnotes", "chapter notes", "chapter-notes"}:
                    containers.append(cand)
                    continue
                # Evt. LLM
                if args.llm:
                    decide = _end_llm_is_endnotes_container(llm, str(cand))
                    if decide:
                        containers.append(cand)

    # --- Finn toppnivå-<section> og (gjen)bruk/lag én endnotes-container ---------
    top = _end_top_level_section(soup)
    main = None

    # Gjenbruk første eksisterende container som 'main'
    for c in containers:
        main = c
        break

    if main is None:
        # Opprett ny tom container
        main = soup.new_tag("section")
        # bruk epub:type=endnotes
        main["epub:type"] = "endnotes"
        # plasser ved slutten av toppnivå-seksjonen (foretrukket), ellers body
        target_parent = top if isinstance(top, Tag) else (soup.body or soup)
        target_parent.append(main)
    else:
        # sørg for at den har korrekt type
        et = _end_etokens(main)
        if "endnotes" not in et:
            # bevar ev. eksisterende epub:type og legg til 'endnotes'
            et2 = " ".join(sorted(et | {"endnotes"})) if et else "endnotes"
            main["epub:type"] = et2

    # Merk idempotens
    main["data-relocated-endnotes"] = "true"

    # --- Flett innhold fra øvrige containere inn i 'main' i dokumentrekkefølge ----
    merged = 0
    for c in containers[1:]:
        if c is main:
            continue
        # flytt alle signifikante barne-noder inn i main
        for ch in list(c.contents):
            if _end_is_significant(ch):
                main.append(ch.extract())
        # fjern tom wrapper
        try:
            c.decompose()
        except Exception:
            pass
        merged += 1

    # --- Flytt enkelt-noter inn i main (hopp over de som allerede ligger i en endnotes-container)
    moved_singles = 0
    for n in singles:
        if not getattr(n, "parent", None):
            continue
        if _end_in_endnotes_container(n):
            # Ligger allerede i en container (kanskje ikke i 'main', men ble evt. koplet inn over)
            continue
        # Flytt inn i 'main'
        try:
            n.extract()
            main.append(n)
            moved_singles += 1
        except Exception:
            pass

    # --- Sørg for at main ligger helt sist i toppnivå-<section> -------------------
    # (…«before the closing of the top-level <section> element».)
    if isinstance(top, Tag) and main.parent is not top:
        # flytt inn i top hvis mulig
        try:
            main.extract()
            top.append(main)
        except Exception:
            pass

    # Hvis main allerede er siste signifikante barn, gjør ingenting; ellers flytt til slutt
    if isinstance(top, Tag):
        if not _end_already_at_end(top, main):
            try:
                main.extract()
                top.append(main)
            except Exception:
                pass
    else:
        # fallback body
        if soup.body and main.parent is not soup.body:
            try:
                main.extract()
                soup.body.append(main)
            except Exception:
                pass

    logger.info("2.12.2 - Done. Merged containers=%d, moved singles=%d", merged, moved_singles)

    # 2.13 Grammar

    # 2.13.1 Sentence analysis
    # TODO: Find common formatting. Here is one example from 861800
    converted_tables = 0
    converted_spans  = 0
    flagged_llm      = 0

    # 1) Tabeller
    for table in list(soup.find_all("table")):
        if table.get("data-sentence-analysis") == "true":
            continue
        try:
            if _looks_like_grammar_table(table):
                p = _table_to_bracketed_p(table, soup)
                if p:
                    table.insert_before(p)
                    table.decompose()
                    converted_tables += 1
                else:
                    if getattr(args, "llm", False):
                        table["data-llm-pending"] = "sentence-analysis"
                        flagged_llm += 1
        except Exception as e:
            logger.debug(f"2.13.1 - Table conversion failed: {e}")

    # 2) Span-baserte avsnitt
    for par in list(soup.find_all("p")):
        if par.get("data-sentence-analysis") == "true":
            continue
        try:
            if _looks_like_span_analysis(par):
                newp = _span_to_bracketed_p(par, soup)
                if newp:
                    par.replace_with(newp)
                    converted_spans += 1
                else:
                    if getattr(args, "llm", False):
                        par["data-llm-pending"] = "sentence-analysis"
                        flagged_llm += 1
        except Exception as e:
            logger.debug(f"2.13.1 - Span conversion failed: {e}")

    logger.info(
        "2.13.1 - Done. Converted tables=%d, converted spans=%d, flagged_for_llm=%d",
        converted_tables, converted_spans, flagged_llm
    )

    # 2.13.2 Conjugation tables
    # TODO: The only relevant thing here is turning the table into
    # a list. Make interactive.
    converted = 0
    flagged   = 0

    if getattr(args, "mathematics", False):
        pass
        logger.info("2.13.2 - Mathematics book detected; skipping conjugation conversion to avoid false positives.")
    else:
        for table in list(soup.find_all("table")):
            try:
                if _convert_conjugation_table(table, soup, logger):
                    converted += 1
                else:
                    # valgfritt: flagg for LLM dersom tabellen *kan* være grammatikk (svak indikasjon)
                    # Her: hvis den har > 2 kolonner og minst 4 rader og 1. kolonne er “ord/enkeltord”
                    rows = list(_iter_rows(table))
                    if getattr(args, "llm", False) and len(rows) >= 4:
                        first_col_texts = []
                        for tr in rows:
                            cells = tr.find_all(["th","td"], recursive=False)
                            if len(cells) >= 2:
                                tok = _normalize_token(_cell_text(cells[0]).strip()).lower()
                                if tok:
                                    first_col_texts.append(tok)
                        # svak indikator: mange korte tokens i kolonne 1
                        shortish = sum(1 for t in first_col_texts if len(t.split()) <= 2 and len(t) <= 12)
                        if shortish >= max(3, len(first_col_texts)//2):
                            table["data-llm-pending"] = "conjugation-candidate"
                            flagged += 1
            except Exception as e:
                logger.debug(f"2.13.2 - Failed on one table: {e}")

    logger.info("2.13.2 - Done. Converted=%d, flagged_for_llm=%d", converted, flagged)

    # 2.14 Poems
    # TODO: Check original formats. This needs to be interactive
    normalized, flagged = 0, 0

    if getattr(args, "mathematics", False):
        # Kun eksplisitt merkede dikt i matte (unngå falske positiver)
        for tag in soup.find_all(["section","div","article"]):
            if _is_poem_explicit(tag):
                try:
                    if _normalize_poem_container(tag, soup, logger=logger):
                        normalized += 1
                except Exception as e:
                    logger.debug(f"2.14 - Failed (math mode) on one poem container: {e}")
    else:
        # Ikke-matte: normaliser eksplisitte, flagg kandidater
        for tag in soup.find_all(["section","div","article","blockquote"]):
            if _is_poem_explicit(tag):
                try:
                    if _normalize_poem_container(tag, soup, logger=logger):
                        normalized += 1
                except Exception as e:
                    logger.debug(f"2.14 - Failed on one poem container: {e}")

        # Flagge mulige dikt (kun hvis LLM er på)
        if getattr(args, "llm", False):
            for p in soup.find_all("p"):
                if p.find_parent("section", class_="poem"):  # allerede håndtert
                    continue
                if len(p.find_all("br")) >= 3 and len(_txt(p)) <= 400:
                    p["data-llm-pending"] = "poem-candidate"
                    flagged += 1

    logger.info("2.14 - Done. Normalized=%d, flagged_for_llm=%d", normalized, flagged)


    # 2.15 Inline language markup
    if not getattr(args, "detect_languages", False):
        logger.info("2.15 - Inline language markup (disabled by --detect-languages)")
    else:
        logger.info("2.15 - Inline language markup")
        base_lang = _doc_lang(soup)
        auto_wrapped = 0
        llm_flagged  = 0

        for tn in list(soup.find_all(string=True)):
            if _should_skip_textnode(tn):
                continue

            # Hvis nærmeste container allerede har lang/xml:lang → anse som korrekt markert.
            if _parent_has_lang(tn):
                continue

            s = str(tn)
            if not s or s.isspace():
                continue

            # Finn ikke-latinske skriptkjøringer
            nonlatin_runs = _find_script_runs(s)

            # Bygg actions for én samlet erstatning
            actions = []
            # 1) wrap ikke-latin
            for st, en, lang in nonlatin_runs:
                # hvis nærmeste etablerte språk allerede samsvarer, hopp
                if _closest_lang(tn, base_lang).startswith(lang):
                    continue
                actions.append({"start": st, "end": en, "kind": "wrap", "lang": lang})

            # 2) (valgfrtt) flagg latin-engelsk-kandidater for LLM
            if getattr(args, "llm", False):
                latin_runs = _find_latin_englishish_runs(s, min_len=12)
                if latin_runs:
                    # unngå overlapping med wrap-områder
                    def overlaps(a, b):
                        return not (a[1] <= b[0] or b[1] <= a[0])

                    filtered = []
                    for st, en in latin_runs:
                        if any(overlaps((st, en), (x["start"], x["end"])) for x in actions):
                            continue
                        filtered.append((st, en))
                    for st, en in filtered:
                        actions.append({"start": st, "end": en, "kind": "flag", "base": _closest_lang(tn, base_lang)})

            if not actions:
                continue

            # Sortér og anvend i én erstatning (unngår NoneType.parent-feilen)
            actions.sort(key=lambda a: a["start"])
            if _apply_runs_replace(soup, tn, actions):
                auto_wrapped += sum(1 for a in actions if a["kind"] == "wrap")
                llm_flagged  += sum(1 for a in actions if a["kind"] == "flag")

        logger.info("2.15 - Done. Auto-wrapped (non-Latin)=%d, flagged_latin_candidates=%d",
                    auto_wrapped, llm_flagged)

    # 2.16 Mathematics
    logger.info('2.16 - Mathematics')
    if args.mathematics or args.science:
        pass # TODO: This section is deprecated, given that MathML is the new standard

    return soup

def run_xslt(input_xml, stylesheet, output_xml, logger):
    
    logger.info("Running XSLT transformation...")
    saxon_command = [
        'java', '-jar', path.join(Path(__file__).parent, 'saxon', 'saxon-he-10.5.jar'),
        '-s:' + input_xml,
        '-xsl:' + stylesheet,
        '-o:' + output_xml,
    ]

    try:
        subprocess.run(saxon_command, check=True)
        logger.info("XSLT transformation successful.")
    except subprocess.CalledProcessError as e:
        logger.error("XSLT transformation failed: %s", e)

def find_production_number(soup, args, logger):
    # Finn produksjonsnummer
    logger.info("Finding production number...")
    production_number = None
    if (meta := soup.find("meta", attrs={"name": "dc:identifier"})) and meta.get("content"):
        return meta["content"].strip()
    else:
        return path.splitext(path.basename(args.input))[0]


# def apply_requirements(soup, logger, folders, args, comic_text_rpc=None):
def convert(args):
    logger = args.logger
    # Les fil og parse som XML/XHTML
    logger.info(f"Applying Statped Mark-up Requirements to file:::: {args.input}")
    
    '''
    if getattr(args, "data", None):
        content = args.data
    else:
        content = Path(args.input).read_bytes()
    '''

    with open(args.input, 'rb') as f:
        content = f.read()

    try:
        soup = BeautifulSoup(content, "xml")

    except Exception:
        # fallback hvis 'xml'-parser ikke er tilgjengelig
        soup = BeautifulSoup(content, "lxml-xml")

    if not 'production_number' in vars(args):
        args.production_number = find_production_number(soup, args, logger)



    tmp = path.join(getcwd(), 'tmp')
    folders = {
            'cwd'       : getcwd(),
            'input'     : path.join(getcwd(), args.input),
            'output'    : path.join(OUTPUT_DIR, args.production_number),
            'logs'      : path.join(getcwd(), 'logs'),
            'static'    : STATIC_DIR,
            'tmp'       : path.join(getcwd(), tmp),
            'source'    : path.join(tmp, 'source'),
            'target'    : path.join(tmp, 'target'),
            'root'      : path.join(tmp, 'target'),
            'epub'      : path.join(tmp, 'target'), #'EPUB'),
            }

    output_folder = path.join(folders['output'], args.production_number)
    rmtree(folders['output'], ignore_errors=True)
    rmtree(folders['logs'], ignore_errors=True)
    rmtree(folders['tmp'], ignore_errors=True)
    #mkdir(folders['output'])
    mkdir(folders['logs'])
    mkdir(folders['tmp'])
    mkdir(folders['source'])
    

    '''
    #epub.extractall(folders['source'])
    copytree(args.input, folders['source'], dirs_exist_ok=True)
    rmtree(path.join(folders['source'], '__MACOSX'), ignore_errors=True)
    copytree(path.join(folders['source']), folders['target'])
    '''

    # TODO: move args.folders to args
    soup = apply_requirements(args, logger, soup, folders)
    #save to file
    rmtree(args.job_dir, ignore_errors=True)
    makedirs(args.job_dir, exist_ok=True)
    with open(args.job_dir / f"{args.production_number}.xhtml", "wb") as f:
        f.write(soup.prettify(formatter="minimal").encode("utf-8"))
    status = "success" # ?
    message = "Fil er konvertert fra xhtml til xhtml med Statped Mark-up Requirements."
    return {"status": status, "message": message}
    #return soup.prettify(formatter="minimal").encode("utf-8")

def convert02(args, logger):
    #production_number = Path(file).stem
    #if not production_number:
    production_number   = path.splitext(path.basename(args.input))[0]
    timestamp = datetime.now().strftime("%Y-%m-%d-%H%M%S%f")
    job_id = f"{production_number}-{timestamp}"
    job_dir = ARTIFACTS_ROOT / job_id

    output_file         = path.join(getcwd(), f'{production_number}.epub')
    old_xhtml_files     = []

    # Set up structure
    # ----------------

    # Open the epub file and extract all the files
    # into a temporary directory
    #with ZipFile(args.input, 'r') as epub:
    tmp = path.join(getcwd(), 'tmp')
    folders = {
            'cwd'       : getcwd(),
            'input'     : path.join(getcwd(), args.input),
            'output'    : path.join(OUTPUT_DIR, production_number),
            'logs'      : path.join(getcwd(), 'logs'),
            'static'    : STATIC_DIR,
            'tmp'       : path.join(getcwd(), tmp),
            'source'    : path.join(tmp, 'source'),
            'target'    : path.join(tmp, 'target'),
            'root'      : path.join(tmp, 'target'),
            'epub'      : path.join(tmp, 'target'), #'EPUB'),
            }

    output_folder = path.join(folders['output'], production_number)
    rmtree(folders['output'], ignore_errors=True)
    rmtree(folders['logs'], ignore_errors=True)
    rmtree(folders['tmp'], ignore_errors=True)
    mkdir(folders['output'])
    mkdir(folders['logs'])
    mkdir(folders['tmp'])
    mkdir(folders['source'])

    #epub.extractall(folders['source'])
    copytree(args.input, folders['source'], dirs_exist_ok=True)
    rmtree(path.join(folders['source'], '__MACOSX'), ignore_errors=True)
    copytree(path.join(folders['source']), folders['target'])

    # Create the soup object
    xhtml_path = find_xhtml(production_number, folders['epub'], logger)
    with open(xhtml_path, 'r') as xhtml:
        soup = BeautifulSoup(xhtml.read(), 'xml')

    # Apply Statped Mark-up Requirements
    # ----------------------------------
    soup = apply_requirements(soup, logger, folders, args)

    # Clean up the soup object
    # ------------------------

    # Remove wrapping sections
    for section in [s for s in soup('section') if s.attrs == {}]:
        section.unwrap()

    # Set pagebreak title
    pagebreaks = [p for p in soup(attrs={'epub:type':'pagebreak'}) if 'title' not in p.attrs.keys()]
    for pagebreak in pagebreaks:
        pagebreak['title'] = pagebreak['aria-label'] if 'aria-label' in pagebreak.attrs.keys() else pagebreaks.index(pagebreak) + 1

    # Remove "relocated" attributes
    for tag in soup(attrs={'relocated':True}):
        del tag['relocated']

    # Remove "relocated_from" attributes
    for tag in soup(attrs={'relocated_from':True}):
        del tag['relocated_from']

    '''
    # Remove <li> wrapping <li>
    for li in soup('li'):
        if li.li:
            li.li.unwrap()
    '''
    
    # Create a new epub file
    # ----------------------
    
    output      = args.output if args.output else path.join(folders['output'], f'{production_number}.epub')
    language    = f'''lang="{soup.html['lang']}" xml:lang="{soup.html['lang']}"'''

    # Save soup into a new xhtml file
    del soup.html['lang'] # TODO: check

    # simple test output
    with open('test.xhtml', 'w') as content:
        content.write(str(soup))


    with open(path.join(folders['epub'], f'{production_number}.xhtml'), 'w') as content:
        content.write(str(soup)) #.replace('<html>', f'<html {correct_html_tag} {language}>'))

    '''
    # Create epub file
    with ZipFile(output_file, 'w') as epub:
        epub.write(path.join(folders['root'], 'mimetype'), 'mimetype')
        for root, _, files in walk(path.join(folders['root'])):
            for file in files:
                if path.join(root, file) != path.join(folders['root'], 'mimetype'):
                    epub.write(path.join(root, file),
                               path.relpath(path.join(root, file), folders['root']),
                               compress_type=ZIP_DEFLATED)
    '''

    # Create nav.xhtml
    # ----------------
    run_xslt(path.join(folders['epub'], f'{production_number}.xhtml'),
             path.join(folders['static'], 'html-to-nav.xsl'),
             path.join(folders['epub'], 'nav.xhtml'),
             logger)

    # Move the new epub file to the output folder
    #move(f'{production_number}.epub', folders['output'])
    copytree(folders['epub'], path.join(folders['output']), dirs_exist_ok=True)

    '''
    # Validate epub
    # -------------
    output = EpubCheck(f'output/{output_file}')
    print(output.valid)
    print(output.messages)
    '''

# MAIN
# ====

def main():
    # Parse command line arguments
    parser = ArgumentParser(description='''
        Convert an epub conforming to the Nordic Guidelines for the 
        Production of Accessible EPUB 3 to an epub conforming to the 
        Statped Mark-up Requirements specification.
        ''')

    parser.add_argument('input',
                        help = 'The input file')
    parser.add_argument('-o',
                        '--output',
                        help = 'The output xhtml file')
    parser.add_argument('-m',
                        '--mathematics',
                        help = 'The epub is a mathematics book',
                        action = 'store_true')
    parser.add_argument('-s',
                        '--science',
                        help = 'The epub is a sience book',
                        action = 'store_true')
    parser.add_argument(
                        '-v', '--verbose',
                        action='count',
                        default=0,
                        help='Increase verbosity: -v=INFO, -vv=DEBUG'
                        )
    parser.add_argument('-t',
                        '--toc-levels',
                        help = 'The number of levels in the table of contents',
                        type = int)
    parser.add_argument('-g',
                        '--grade',
                        help = 'The grade level of the book',
                        type = int)
    parser.add_argument('-p',
                        '--p-length',
                        help = 'The maximum length of a small paragraph',
                        type = int)
    parser.add_argument('-l',
                        '--link_footnotes',
                        help = 'Link to footnotes in the text',
                        action = 'store_true')
    parser.add_argument('--relocate',
                        dest='relocate',
                        help='Relocate elements per §2.1.2 (default: on)',
                        action='store_true',
                        default=True)
    parser.add_argument('--no-relocate',
                        dest='relocate',
                        help='Disable relocation step (§2.1.2)',
                        action='store_false')
    parser.add_argument('--llm',
                        dest='llm',
                        help='Use local LLM (via RabbitMQ) for nuanced §2.1.2 decisions',
                        action='store_true',
                        default=False)
    parser.add_argument('-a',
                        '--aggressive',
                        help='Convert tables (§2.5.1.18) more aggressively',
                        action='store_true',
                        default=False)
    parser.add_argument('--plays',
                        dest='plays',
                        help='Apply §2.8.1 (plays/screenplays) transforms. Default OFF.',
                        action='store_true')
    parser.add_argument('--cleanup-plays',
                        dest='cleanup_plays',
                        help='Cleanup false play markup (remove wrong class="play", bogus speaker/directions).',
                        action='store_true')
    parser.add_argument('--table-normalize-cell-lists',
                        help='Normalize multi-item text inside table cells to <ul class="list-unstyled"> when safe.',
                        action='store_true')
    parser.add_argument('--detect-languages',
                        dest='detect_languages',
                        help='Auto-tag inline language/script changes (§2.15)',
                        action='store_true')

    args = parser.parse_args()
    #configure_logging(args.verbose)

    # Set up logger
    logger = getLogger(__name__)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[logging.StreamHandler(sys.stdout)]
    )
    logger = logging.getLogger(__name__)

    logging.getLogger("aio_pika").setLevel(logging.WARNING)
    logging.getLogger("aiormq").setLevel(logging.WARNING)

    with open(args.input, 'rb') as f:
        args.data = f.read()

    args.job_id = '0000'
    args.job_dir = ARTIFACTS_ROOT / args.job_id

    args.logger = logger
    # Convert epub
    convert(args)


if __name__ == '__main__':
    main()
