#!/usr/bin/env python3
"""Reuse the frozen serial 1GiB PDF builder at the new complete receiving target."""
from pathlib import Path
import importlib.util
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('frozen_q214_pdf_builder',ROOT/'research/quartic214-manuscript/build_pdf.py')
builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
builder.HERE=HERE
builder.ROOT=ROOT
if __name__=='__main__':builder.main()
