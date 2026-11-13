# period-map results log

Task period-map (2026-11-13). Base 322303a2. Targets: `PeriodMapGlue`, `HauptmodulUnique`, `QMDenZeroCM3`
(scratch/fibre-qm-period/part_fqm.lean, namespace `HSyn.G0Split.FibreQM`).

## Setup
- `origin/wip/r1b-state` (f90cf864): no report `docs/research/r1b-state.md` on the branch at 06:40. Nothing to compare yet.
- prereq `lake build ZInQKernel.HDecomp.Analytic.QMLattice ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`: OK 1m22s.
- `build_base.sh`: `PMBase.lean` = fibre-qm-period's `FibreQM.lean` verbatim, compiled to `olean/PMBase.olean` (2m56s, 0 errors;
  its own axioms lines standard). (First attempt via `apply_edit.py` failed: the edit is already in g0-thetapoint's file; not used.)
- `light_base.lean`: g0-thetapoint `ThetaPoint.lean` lines 77-289 (PkgI1 section) verbatim + verbatim `QMHauptmodulFn`,
  `qmHauptmodul_iff`, `QMDenZeroCM3`, `IsHolP1At`, `GammaStarFibresCM`, `IsGammaStarHauptmodul`, `HauptmodulUnique` from
  part_fqm.lean. Imports Mathlib only. Compiled to `olean/PMLightBase.olean` (7s, 0 errors).

## Numerics (py/al_weight.py, output al_weight_out.txt) VERIFIED
- iota multiplicative on the basis (sympy): True.
- The form of weight 8 is `S/dF^4`, `S = Σθ_m^8∘Ω`, `dF = (τ-3)(τ+1)` (NOT `S·dF^4` as fibre-qm-period's report §4 says;
  its printed formula |S(γτ)/S(τ)| = |cτ+d|^8 |dF(τ)/dF(γτ)|^4 is right and its output rows `detF'^(-4)` give 1.0).
- `|G8(γτ)| det(γ)^4 / (|cτ+d|^8 |G8(τ)|) = 1.0` (10+ digits) for the Atkin–Lehner elements x = j (nrd 3), 2+i (nrd 2),
  2j+ij (nrd 6), 1+j (nrd 4), each normalizing 𝒪 (sympy check), at τ = 0.3+1.1i, -0.7+0.9i. With fibre-qm-period's norm-1
  checks: G8 has weight 8 for all of Γ* (automorphy factor (cτ+d)/√det γ).
- x' = 1/2 + (3/2)j + ij = (2+i)(1+j)/2(2+i)^{-1} ∈ 𝒪, x'^2 - x' + 1 = 0, fixes (3+2√2)i√3, ord S there ≈ 2.00001 (not needed in the end).
- `S(Ω(√2+i)) = -33.9079295761…` (≠ 0).

## Lean: light part (DevLight.lean = import PMLightBase + part_light.lean)
- run_light1: errors (ambiguous `I` with UpperHalfPlane.I, pow shapes, ring residuals). Fixed.
- run_light2: 3 errors. Fixed.
- run_light3: 0 errors. All 9 `#print axioms` lines `[propext, Classical.choice, Quot.sound]`. VERIFIED.
  Proved: `isHolP1At_of_hauptFn`, `cm4_exists`, `cm3_exists`, `cm24_exists`, `hauptmodulUnique_of`, `iota_mul`,
  `gammaStar_inv`, `cm3_of_equiv`, `qmDenZeroCM3_of`.
  * `hauptmodulUnique_of : ThetaOmegaAnalytic → S8Nonzero → SphereFactorAffine → HauptmodulUnique`
  * `qmDenZeroCM3_of : ThetaOmegaAnalytic → S8Nonzero → S8Weight8 → S8OrderCM3 → ValenceBoundGammaStar → QMDenZeroCM3`
