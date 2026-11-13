"""Check that scratch/ts-sn/TSSN.lean starts with scratch/prop-ts-glue/PropTSGlue.lean byte for byte."""
import sys, pathlib
root = pathlib.Path(__file__).resolve().parents[2]
a = (root / "scratch/prop-ts-glue/PropTSGlue.lean").read_bytes()
b = (root / "scratch/ts-sn/TSSN.lean").read_bytes()
print("PREFIX IDENTICAL" if b.startswith(a) else "PREFIX DIFFERS")
