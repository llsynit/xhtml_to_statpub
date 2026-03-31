import logging, sys, re

from logging            import getLogger, DEBUG, INFO, WARNING, StreamHandler, Formatter
from argparse           import ArgumentParser
from bs4                import BeautifulSoup, NavigableString, Comment, Tag
from lxml               import etree

DEFAULT_GRADE = 10
STATIC_FOLDER = 'static'
CSS_FILE = 'ebok.css'

# =============== APPLY REQUIREMENTS ================

def apply_requirements(args, soup):
    args.logger.info(f"Applying Statped Mark-up Requirements to file:::: {args.input}")

    if args.grade:
        try:
            args.grade = int(args.grade)
        except:
            args.logger.error(f'Grade is set to other than number: {args.grade}. Using default grade: {DEFAULT_GRADE}')
            args.grade = DEFAULT_GRADE
    else:
        args.grade = DEFAULT_GRADE

    # 2.1.1 CSS — ensure exact Statped requirement
    args.logger.info('2.1.1 - Ensuring ebok.css link in <head>')

    head = soup.head
    if head is None:
        head = soup.new_tag('head')
        # sørg for at head havner tidlig i dokumentet
        if soup.html:
            soup.html.insert(0, head)
        else:
            soup.insert(0, head)

    # Fjern andre stylesheets for å unngå konflikter
    links = 0
    styles = 0
    for link in head('link', attrs={'rel':'stylesheet'}):
        link.decompose()
        links += 1
    for style in head('style'):
        style.decompose()
        styles += 1
    args.logger.warning(f'2.1.1 - Removed {links} stylesheet link(s) and {styles} style definition(s)')

    try:
        with open(CSS_FILE, 'r') as f:
            css_content = f.read()
        style_tag = soup.new_tag('style')
        style_tag.string = css_content
        args.logger.info(f'2.1.1 - Added content of {CSS_FILE} in style tag')
    except:
        args.logger.warning(f'2.1.1 - Could not load {CSS_FILE}')

    # 2.1.2 Relocation of elements
    # 1. Figures (images) - See 2.3.5
    # 2. Aside elements in general - See 2.6
    # 3. Glossaries/ Description lists (whether placed in an aside or not) - See 2.4.4.2

    # 2.1.3 Uppercase text
    # TODO: solve:
    # <h5 id="Sec-0714">Anne Franks dagbok</h5>
    # <h5 id="Sec-0714">Anne franks dagbok</h5>

    args.logger.info('2.1.3 - Uppercase text')

    for node in soup(string=True):
        if node.parent.name in ['script', 'style'] or isinstance(node, NavigableString) == False:
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

    # 2.1.4 Blank pages in the original source
    args.logger.info('2.1.4 - Handling consecutive pagebreaks as blank pages')
    for pagebreak in soup(attrs={'class': 'pagebreak'}):
        if (next_sibling := pagebreak.find_next_sibling()) and next_sibling.get('class') == 'pagebreak':
            args.logger.info('2.1.4 - Found consecutive pagebreaks, inserting blank page marker')
            blank_p = soup.new_tag('p')
            blank_p.string = 'Blank side.'
            next_sibling.insert_before(blank_p)
            pagebreak.decompose()

    # 2.1.5 Blank pages where elements have been moved
    # Implement this when moving elements in 2.3.5, 2.4.4.2 and 2.6
    args.logger.info('2.1.5 - Handling blank pages where elements have been moved (to be implemented in later steps)')

    # 2.1.6 Use of <em> and <strong>
    EMPH_TYPES = ['em', 'strong']

    # 2.1.6.1 Do not use double emphasis
    args.logger.info('.2.1.6.1 - Removing double emphasis (nested <em> or <strong>)')
    for emphasis in soup(EMPH_TYPES):
        for parent in emphasis.parents:
            if parent.name in EMPH_TYPES:
                emphasis.unwrap()

    # 2.1.6.2 Headings in <em> or <strong>
    args.logger.info('2.1.6.2 - Unwrapping headings from <em> or <strong>')
    for heading in soup(re.compile('^h[1-6]$')):
        for emphasis in heading(EMPH_TYPES):
            emphasis.unwrap()

    # 2.1.6.3 Use of <em> or <strong> in words and expressions
    args.logger.info('2.1.6.3 - Removing <em> and <strong> from words and expressions')
    punctuation = r'[.,;:!?()"\']'
    for emphasis in soup(EMPH_TYPES):
        if (emphasis.string and
                len(emphasis.string) > 1 and
                emphasis.string[-1] in punctuation and
                (previous_sibling := emphasis.previous_sibling) and
                previous_sibling.string and
                previous_sibling.string.strip() and
                not previous_sibling.string.strip()[-1] in punctuation):
            emphasis.insert_after(emphasis.string[-1])
            emphasis.string = emphasis.string[:-1]

    # 2.1.6.4 Paragraphs in <em> or <strong>
    args.logger.info('2.1.6.4 - Unwrapping paragraphs from <em> or <strong>')
    for p in soup('p'):
        if len(list(p.children)) == 1 and p.em:
            p.em.unwrap()

    # 2.1.6.5 Avoid use of <em> or <strong> in description lists
    args.logger.info('2.1.6.5 - Unwrapping <em> and <strong> from description lists')
    for dl in soup('dl'):
        for emphasis in dl(EMPH_TYPES):
            emphasis.unwrap()

    # 2.1.6.6 Avoid use of <em> or <strong> in table headings
    args.logger.info('2.1.6.6 - Unwrapping <em> and <strong> from table headings')
    for th in soup('th'):
        for emphasis in th(EMPH_TYPES):
            emphasis.unwrap()

    # 2.1.6.7 Avoid use of <em> or <strong> in figures and figcaptions
    args.logger.info('2.1.6.7 - Unwrapping <em> and <strong> from figures and figcaptions')
    for figure in soup('figure'):
        for emphasis in figure(EMPH_TYPES):
            emphasis.unwrap()

    # 2.1.7 Non-breaking space
    args.logger.info('2.1.7 - Replacing non-breaking spaces with regular spaces')

    NBSP = "\u00A0"
    prefixes = [r"§{1,2}",r"kap\.",r"pkt\.",r"nr\.",r"s\.",r"fig\.",r"tab\.",r"vedl\.",
        r"kl\.",r"ca\.",r"maks\.",r"min\.",r"kr",r"NOK",r"EUR",r"USD",r"GBP",r"€",r"\$",r"£",]
    units = [r"kg",r"g",r"mg",r"m",r"cm",r"mm",r"km",r"l",r"dl",r"ml",r"°C",
        r"°F",r"V",r"A",r"W",r"Hz",r"kHz",r"MHz",r"GHz",r"KB",r"MB",r"GB",r"TB",r"%"]

    prefix_pattern = re.compile(rf"\b({'|'.join(prefixes)})\s+(?=\d)", flags=re.IGNORECASE)
    unit_pattern = re.compile(rf"(?<=\d)\s+({'|'.join(units)})\b")
    symbol_pattern = re.compile(r"(?:(§{1,2})|(€)|(\$)|(£))\s+(?=\d)")
    skip_tags = {"script", "style"}

    for text_node in soup.find_all(string=True):
        parent = text_node.parent
        if parent and parent.name in skip_tags:
            continue

        original = str(text_node)
        updated = original
        updated = prefix_pattern.sub(lambda m: f"{m.group(1)}{NBSP}", updated)
        updated = symbol_pattern.sub(lambda m: f"{m.group(0).rstrip().split()[0]}{NBSP}",updated)
        updated = unit_pattern.sub(lambda m: f"{NBSP}{m.group(1)}",updated)

        if updated != original:
            new_node = NavigableString(updated)
            text_node.replace_with(new_node)

    # 2.1.8 Table of contents
    args.logger.info('2.1.8 - Handling table of contents')

    if (toc := soup.find('section', attrs={'epub:type': 'frontmatter toc'})):
        for figure in toc('figure'):
            figure.decompose()
        for parent in toc.parents:
            if parent.name == 'table':
                pass # TODO: implement relocation of toc out of tables
        # Cases are solved in 2.1.3 Uppercase text 
        if (ol := toc.find('ol')): # TODO: improve
            if 'list-style-type-none' not in ol.get('class', []):
                args.logger.warning('2.1.8 - Wrong class on <ol> in table of contents')
            if 'list-style-type: none' not in ol.get('style', '').replace(' ', '').replace(';', ';'):
                args.logger.warning('2.1.8 - Wrong style on <ol> in table of contents')
        else:
            args.logger.warning('2.1.8 - No <ol> found in table of contents')

    return soup

# =============== MAIN ================

def convert(args):
    args.logger.info('Converting file to Statpub')

    with open(args.input, 'rb') as f:
        content = f.read()

    try:
        soup = BeautifulSoup(content, "xml")

    except Exception:
        # fallback hvis 'xml'-parser ikke er tilgjengelig
        soup = BeautifulSoup(content, "lxml-xml")

    soup = apply_requirements(args, soup) 

    return soup

# =============== MAIN ================

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
                        help = 'The output epub file')
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

    args.logger = logger
    soup = convert(args)
    output = args.output if args.output else 'output.xhtml'

    with open(output, 'wb') as f:
        f.write(soup.prettify(formatter='minimal').encode('utf-8'))
        logger.info(f'Wrote converted file to {output}')

if __name__ == '__main__':
    main()
