"""Assemble scratch/hecke-rest/FibreSizes.lean from verbatim line ranges of
scratch/ts-hecke/TSHecke.lean and the new part FibreSizesMain.lean.part.
Run from the repository root: ~/pyenv/bin/python -I scratch/hecke-rest/assemble.py"""
import sys

SRC = "scratch/ts-hecke/TSHecke.lean"
src = open(SRC, encoding="utf-8").read().split("\n")

def rng(a, b):  # 1-indexed inclusive
    return "\n".join(src[a - 1:b])

HEADER = """import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Textbook.SkolemNoether

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: `HeckeFibreSizes` (assembled by `scratch/hecke-rest/assemble.py`)

Verbatim copies from `scratch/ts-hecke/TSHecke.lean` (checked by `check_identical.py`):
lines 3563-4606 (aut-o-finite's `Aut(𝒪)/Inn(𝒪^×)`), 5511-5717 (ts-hecke's `Units.lean`),
and inside `namespace TSHecke`: 6132-6135 (`twistFibre`), 6154-6213 (`section Count`),
6215-6227 (`exists_sub_liftO`), 6553-6577 (`HeckeFibreSizes`, the target). New work below the
second banner. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/
"""

TSH_OPEN = """
noncomputable section

namespace TSHecke

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin PkgI3
open MonoidalCategory CartesianMonoidalCategory MonObj
"""

parts = [HEADER, rng(3563, 4606), "", rng(5511, 5717), TSH_OPEN, rng(6132, 6135), "",
         rng(6154, 6213), "", rng(6215, 6227), "", rng(6553, 6577), "", "end TSHecke", "", "end", ""]
main = open("scratch/hecke-rest/FibreSizesMain.lean.part", encoding="utf-8").read()
out = "\n".join(parts) + "\n" + main
open("scratch/hecke-rest/FibreSizes.lean", "w", encoding="utf-8").write(out)
print("wrote", out.count("\n"), "lines")
