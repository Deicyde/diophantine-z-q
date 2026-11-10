"""Print the extracted text of pages a..b of a PDF (for reading only; nothing is saved).
Usage: uv run --with pypdf --with fonttools python -I pdf_page.py FILE.pdf a b"""
import logging, sys
logging.disable(logging.WARNING)
from pypdf import PdfReader
r = PdfReader(sys.argv[1])
for i in range(int(sys.argv[2]) - 1, int(sys.argv[3])):
    print(f"=== page {i+1}")
    print(r.pages[i].extract_text())
