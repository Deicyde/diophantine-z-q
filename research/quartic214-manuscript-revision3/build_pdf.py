#!/usr/bin/env python3
"""Use the retained serial, resource-limited PDF builder for revision 3."""
from pathlib import Path
import importlib.util

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('retained_pdf_builder', ROOT / 'research/quartic214-manuscript/build_pdf.py')
builder = importlib.util.module_from_spec(spec)
spec.loader.exec_module(builder)
builder.HERE = HERE
builder.ROOT = ROOT
if __name__ == '__main__':
    builder.main()
