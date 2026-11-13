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

# ---- NoVert.lean: prop-ts prefix (lines 6-889) + HeckeNoVertRam (3427-3437) + new part
HEADER2 = """import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: `HeckeNoVertRam` (assembled by `scratch/hecke-rest/assemble.py`)

Verbatim copies from `scratch/ts-hecke/TSHecke.lean`: lines 6-889 (the prop-ts prefix:
`NoVerticalRam`, `intPolyAlg`, `vertPrime`, `NormalizationModel`, ...) and, inside
`namespace PropTSGlue`, lines 3427-3437 (`HeckeNoVertRam`, the target). New work below the
second banner. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/
"""
GLUE_OPEN = """
open CategoryTheory AlgebraicGeometry Limits
open LeafQM.AV GlueDescent.B2Q

noncomputable section

namespace PropTSGlue

open Polynomial G0ModField PropTSRed
"""
parts2 = [HEADER2, rng(6, 889), GLUE_OPEN, rng(3427, 3437), "", "end PropTSGlue", "", "end", ""]
main2 = open("scratch/hecke-rest/NoVertMain.lean.part", encoding="utf-8").read()
out2 = "\n".join(parts2) + "\n" + main2
open("scratch/hecke-rest/NoVert.lean", "w", encoding="utf-8").write(out2)
print("wrote NoVert", out2.count("\n"), "lines")

# ---- CurveChart.lean: prop-ts prefix + image-plane value calculus + CurveNormChart + new part
ip = open("scratch/image-plane/AlgDepProof.lean", encoding="utf-8").read().split("\n")
def irng(a, b):
    return "\n".join(ip[a - 1:b])
HEADER3 = """import Mathlib
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.Descent.B2Glue

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: `CurveNormChart` (hence `CurveGaloisChart`) reduced to two statements of curve
theory (assembled by `scratch/hecke-rest/assemble.py`)

Verbatim copies: `scratch/ts-hecke/TSHecke.lean` lines 6-889 (prop-ts prefix, with
`NormalizationModel`) 6444-6455 (`CurveNormChart`) and 6526-6551 (`NormalizationModelInf`, `CurveChartInf`), the
targets, inside `namespace TSHecke`;
`scratch/ts-hecke/TSHecke.lean` lines 4613-5002 and 5010-5173 (infra-smooth-dim's stalk dimensions,
curve-glue's `isDomain_of_dim_one`), 5725-5858 (ts-hecke's `exists_qbar_point`,\n`eq_of_forall_qbar`); `scratch/image-plane/AlgDepProof.lean` lines 15-171 and 277-322 (the value calculus `ptOf`, `ev`,
`ev_res`, `ev_comp`, `ev_spec_top`, `val_of_mem`, ...). New work below the last banner.
No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/
"""
TSH2 = """
noncomputable section

namespace TSHecke

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PkgI3
"""
parts3 = [HEADER3, rng(6, 889), "", irng(15, 171), "", irng(277, 322), "",
          "end ImagePlane", "", "end Pin", "", "end AV", "", "end LeafQM", "", "end", "",
          rng(4613, 5002), "", rng(5010, 5173), "", rng(5725, 5858), "", "end TSHeckeGal", "", "end", "",
          TSH2, rng(6444, 6455), "", rng(6526, 6551), "", "end TSHecke", "", "end", ""]
main3 = open("scratch/hecke-rest/CurveChartMain.lean.part", encoding="utf-8").read() + "\n" + \
    open("scratch/hecke-rest/InfFnMain.lean.part", encoding="utf-8").read()
out3 = "\n".join(parts3) + "\n" + main3
open("scratch/hecke-rest/CurveChart.lean", "w", encoding="utf-8").write(out3)
print("wrote CurveChart", out3.count("\n"), "lines")

# ---- HeckeRestAll.lean: all of TSHecke.lean + image-plane value calculus + the three new parts
HEADER4 = """
/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: the integrated file (assembled by `scratch/hecke-rest/assemble.py`)

Above: `scratch/ts-hecke/TSHecke.lean`, all 7109 lines, verbatim. Below: the value calculus of
`scratch/image-plane/AlgDepProof.lean` (lines 15-171, 277-322, verbatim) and the new parts of
`FibreSizes.lean`, `NoVert.lean`, `CurveChart.lean` (their `*Main.lean.part` files, verbatim),
then the composite theorems. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/
"""
COMPOSITE = open("scratch/hecke-rest/AllMain.lean.part", encoding="utf-8").read()
parts4 = ["\n".join(src), HEADER4, irng(15, 171), "", irng(277, 322), "",
          "end ImagePlane", "", "end Pin", "", "end AV", "", "end LeafQM", "", "end", "",
          open("scratch/hecke-rest/FibreSizesMain.lean.part", encoding="utf-8").read(),
          main2, main3, COMPOSITE]
out4 = "\n".join(parts4)
open("scratch/hecke-rest/HeckeRestAll.lean", "w", encoding="utf-8").write(out4)
print("wrote HeckeRestAll", out4.count("\n"), "lines")
