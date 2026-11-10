"""Extract text from a PDF (pypdf) and print lines matching a regex, with page numbers.
Usage: uv run --with pypdf python -I pdf_grep.py FILE.pdf REGEX [first_page last_page]
Prints only matching lines (short context); the PDF itself is never copied."""
import logging, re, sys
logging.disable(logging.WARNING)
from pypdf import PdfReader
f, pat = sys.argv[1], re.compile(sys.argv[2])
r = PdfReader(f)
a = int(sys.argv[3]) if len(sys.argv) > 3 else 1
b = int(sys.argv[4]) if len(sys.argv) > 4 else len(r.pages)
for i in range(a - 1, b):
    t = r.pages[i].extract_text() or ""
    for line in t.splitlines():
        if pat.search(line):
            print(f"p{i+1}: {line[:200]}")
