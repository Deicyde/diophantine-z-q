"""leaf-adopt: insert the compiled report files into scratch/h-decomposition/Leaves.lean.

Run once on the hsyn-fold version of Leaves.lean (it inserts four sections before the
`noncomputable section` / `namespace HSyn` block). Later edits to Leaves.lean were by hand.
Usage: python3 scratch/leaf-adopt/fold.py  (from the worktree root)."""
import re, sys

LEAVES = "scratch/h-decomposition/Leaves.lean"

def body(path, first, drop=(), subs=()):
    lines = open(path).read().split("\n")
    out = []
    for i, l in enumerate(lines, start=1):
        if i < first:
            continue
        if any(a <= i <= b for a, b in drop):
            continue
        if l.startswith("#print axioms"):
            continue
        for a, b in subs:
            l = l.replace(a, b)
        out.append(l)
    return "\n".join(out).rstrip() + "\n"

def wrap(name, origin, text, close_anon):
    return (f"section {name}\n/-! ### leaf-adopt (2026-11-12): copied from `{origin}` (compiled there).\n"
            f"Only changes: imports and `#print axioms` lines dropped"
            + ("; see the section's note for renamings" if "QMLeaves" in origin or "T32a" in origin else "")
            + ". -/\n\n" + text + ("end\n" if close_anon else "") + f"\nend {name}\n\n")

t32a = body("scratch/glue-t32a/T32a.lean", 18, drop=[(1473, 1506), (1612, 1632)])
qm = body("scratch/leaf-qm-fp/QMLeaves.lean", 9,
          subs=[("GlueA6Alg.goodReduction_of_QM_rational3'", "PkgI2.goodReduction_of_QM_rational3'")])
mc = body("scratch/leaf-modcurves/ModCurveLeaves.lean", 4)
fa = body("scratch/def-faltings/Faltings.lean", 2)

ins = (wrap("GlueT32aSec", "scratch/glue-t32a/T32a.lean", t32a, False)
       + wrap("LeafQMSec", "scratch/leaf-qm-fp/QMLeaves.lean", qm, True)
       + wrap("LeafModCurvesSec", "scratch/leaf-modcurves/ModCurveLeaves.lean", mc, True)
       + wrap("DefFaltingsSec", "scratch/def-faltings/Faltings.lean", fa, False))

src = open(LEAVES).read()
anchor = "end LeafPushSec\n"
assert src.count(anchor) == 1
src = src.replace(anchor, anchor + "\n" + ins, 1)
open(LEAVES, "w").write(src)
print("inserted", ins.count("\n"), "lines")
