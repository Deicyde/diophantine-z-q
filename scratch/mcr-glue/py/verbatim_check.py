"""Check that MCRGlue.lean = ModelGlue6.lean (verbatim) + the mcr-glue parts, and that the target
definition `def ModelCoordinateResidue` occurs exactly once (in the verbatim prefix)."""
import sys, pathlib
root = pathlib.Path(__file__).resolve().parents[3]
base = (root / "scratch/model-glue/ModelGlue6.lean").read_text()
parts = [(root / f"scratch/mcr-glue/MCRGlue{i}.lean.part").read_text() for i in (1, 2, 3, 4)]
full = (root / "scratch/mcr-glue/MCRGlue.lean").read_text()
ok = True
if full != base + "".join(parts):
    print("FAIL: MCRGlue.lean is not ModelGlue6.lean + parts"); ok = False
n = full.count("def ModelCoordinateResidue : Prop")
if n != 1 or "def ModelCoordinateResidue : Prop" not in base:
    print("FAIL: target definition count", n); ok = False
for i, p in enumerate(parts, 1):
    if "sorry" in p or "\naxiom " in p:
        print(f"FAIL: part {i} contains sorry/axiom"); ok = False
print("ALL OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
