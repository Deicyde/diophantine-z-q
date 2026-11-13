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

## Lean: heavy part (DevHeavy.lean = import PMBase + part_light.lean + part_heavy.lean)
- Finding: the committed `scratch/fibre-qm-period/FibreQM.lean` predates part_fqm.lean's last step (no
  `qmSkolemNoetherC_proof`, `fibreQMPeriod_main`). `build_base.sh` now takes FibreQM.lean lines 1-20634 (through part_pin)
  + the current part_fqm.lean. run_base2: 0 errors, 2m49s, 47 axioms lines, none with sorryAx. VERIFIED.
- run_heavy1-3: errors (`O` → `LeafQM.O`; `one_mul` ambiguous with `MonObj.one_mul` under the heavy opens). Fixed.
- run_heavy4: 0 errors; `periodMapGlue_of`, `periodMapGlue_own`, `fibreQMPeriod_periodMap` axioms
  `[propext, Classical.choice, Quot.sound]` (and the 9 light ones again). VERIFIED.
  * `periodMapGlue_of Y Φ π : R1fpProps Y Φ → BaseChangeClassUnique → PiTwistC Y Φ π → QMTwistLattice → PiCMC Y Φ π →
    CMFixedHasCM → PeriodMapGlue Y Φ π`
  * `fibreQMPeriod_periodMap`: `ThetaPt.FibreQMPeriod` from fibre-qm-period's leaves and the new named pieces.
- run_heavy5-10: `cmFixedHasCM_of : T11aRiemannEnd → CMFixedHasCM` developed (errors: `DiscreteTopology` instance of
  `qmLattice` not found through `set`/in PMBase's context — supplied by `haveI … unfold qmLattice; infer_instance`;
  rewriting details in `Module.End`). A python edit accidentally dropped the tail of part_heavy.lean once; restored from
  HEAD and re-applied.
- run_heavy11: 0 errors; `cmFixedHasCM_of`, `periodMapGlue_of`, `periodMapGlue_own`, `fibreQMPeriod_periodMap` axioms
  standard. VERIFIED. `fibreQMPeriod_periodMap` now uses `cmFixedHasCM_of hR11` (T11a is already a hypothesis), so
  `CMFixedHasCM` is no longer a hypothesis.

## r1b-state comparison (origin/wip/r1b-state 07669d97, read 07:10)
- r1b-state's leaf: `R1bState.R01b_ComplexUniformization' := ∃ Y Φ, R1fpProps Y Φ ∧ R1bProps Y Φ`; `R1bProps` = (a) every
  `P : QML3 ℂ` has a QM-compatible uniformization by some `Λ_τ` (bp-analytic `Uniformization.IsUniformization` of
  `Torus Λ_τ ≃+ P.A(ℂ)`, `qmAct`-compatible); (b) `y : ℂ → Y(ℂ)` with `Φ_ℂ(y τ) = [P_τ]`, `P_τ` QM-uniformized by `Λ_τ`
  carrying the torus's level structure `a ↦ [ι(a)(τ,1)ᵀ/3]` to `η` (`IsQMUnifLevel`); (c) every regular function on every
  Zariski open is holomorphic along `y`. VERIFIED (read R1b.part).
- fibre-qm-period's `R1bFamily Y Φ π`: `∃ yτ : ℍ → Y(ℂ)`, object at `yτ τ` has an `IotaCompatible` CPts-`IsUniformization`
  with kernel `Λ_τ`, `τ ↦ π(yτ τ)` continuous and `IsHolP1At`. Weaker: no level structure, holomorphy only of `π ∘ y`,
  mentions the triple's `π`.
- Verdict: r1b-state's statement is the published shape (Shimura's holomorphic `φ : ℍ → V(ℂ)` with its moduli
  interpretation, intrinsic, no `π`); `R1bFamily` is a consequence of it plus a bridge (bp-analytic's uniformization ⇒
  CPts uniformization; `HolomorphicP1On` ⇒ `IsHolP1At` + continuity; r1b-state's `q3_form_of_R1bProps` and
  `r1bProps_of_leaf` do the holomorphy and transfer steps). Not compiled across the two files (different AbVar layers:
  build modules vs the ThetaPoint scratch copy).
- gen_check.py (gen_check_out.txt): order-4 elliptic generator 1+i+j (nrd 2, fixes √2+i) ratio 1.0 at two points;
  PSL2 orders: μ 2, 1+i+j 4, j(1+j)/2 6. VERIFIED numerically.
- verbatim_check.py: PkgI1 block and the 6 part_fqm defs in light_base.lean are verbatim. VERIFIED.
- run_light_full: `lake env lean scratch/period-map/PMLight.lean` (light_base + part_light): 0 errors, 9s, 9 axioms lines
  standard. VERIFIED.
- Report docs/research/period-map.md written.

## ThetaOmegaAnalytic (part_theta.lean)
- omega_sym.py (omega_sym_out.txt, sympy): Ω(τ) symmetric; det Im Ω = 12y²/(|τ-3|²|τ+1|²); (Im Ω)₁₁ =
  2y((4-√2)|τ|² - 6√2x + 12 + 3√2)/(|τ-3|²|τ+1|²) > 0 (discriminant 72-168<0). So `OmegaSiegel` VERIFIED (computation).
- run_theta1-2: errors (Summable congr shape, nlinarith, Eventually.and on a mem_nhds, `fun_prop` whnf timeout on the
  theta term). Fixed (manual DifferentiableAt.fun_sum / cexp chain).
- run_theta3: 0 errors; `thetaOmegaAnalytic_of : OmegaSiegel → ThetaOmegaAnalytic`, axioms standard. VERIFIED.
- run_light_full2: `lake env lean scratch/period-map/PMLight.lean` (light_base + part_light + part_theta): 0 errors, 12s,
  all axioms lines standard. VERIFIED.

## OmegaSiegel (part_siegel.lean)
- omega_lean.py (omega_lean_out.txt): with s = √2 symbolic, adj(F₀P⁻¹)E reduced mod s²-2 (`Nf`), det = -s(τ-3)(τ+1)/2,
  A_ij = Im(N_ij conj d): A00 = (y/2)Q, A11 = yQ, Q = (4-s)(x²+y²) - 6sx + 12 + 3s; A00A11 - A01² = 3y²|τ-3|²|τ+1|²;
  quotients by s²-2 for each `linear_combination`. VERIFIED (sympy).
- run_siegel1: 2 errors (omega_eq final step; det_A stated with ^2 vs a*a). Fixed.
- run_siegel2: 0 errors; `omegaSiegel_proof : OmegaSiegel`, `thetaOmegaAnalytic_proof : ThetaOmegaAnalytic`,
  `hauptmodulUnique_of' : S8Nonzero → SphereFactorAffine → HauptmodulUnique`,
  `qmDenZeroCM3_of' : S8Nonzero → S8Weight8 → S8OrderCM3 → ValenceBoundGammaStar → QMDenZeroCM3`; axioms standard. VERIFIED.
- run_heavy12: DevHeavy = import PMBase + part_light + part_theta + part_siegel + part_heavy: 0 errors, 18 axioms lines,
  none with sorryAx; `fibreQMPeriod_periodMap` no longer takes `ThetaOmegaAnalytic`. VERIFIED.
- run_light_full3: lake env lean PMLight.lean (light_base+part_light+part_theta+part_siegel): see run_light_full3.txt

## S8WeightExact ⇒ S8Weight8, S8OrderCM3 (part_order.lean)
- multiplier.py (multiplier_out.txt): the complex multiplier χ(γ) = G8(γτ)det γ⁴/((cτ+d)⁸G8(τ)) is 1 (9-40 digits) for
  (1+j)/2, j, i+j, 3+2i, μ, 1+i+j, 2+i at two points. VERIFIED numerically. New glue `S8WeightExact` (exact automorphy,
  trivial multiplier) replaces `S8Weight8` and `S8OrderCM3`.
- run_order1-4: errors (Exists projections, set-variables in simpa, calc layout, field_simp side goal). Fixed.
- run_order5: 0 errors; `s8Weight8_of : S8WeightExact → S8Weight8`, `s8OrderCM3_of : ThetaOmegaAnalytic → S8WeightExact →
  S8OrderCM3` (G8(τ₃)=w⁸G8(τ₃), w⁸≠1; derivative at τ₃ gives G8'(τ₃)(1-w¹⁰)=0, w¹⁰=-w; order ≥ 2 via
  analyticOrderAt_eq_natCast), `qmDenZeroCM3_of'' : S8Nonzero → S8WeightExact → ValenceBoundGammaStar → QMDenZeroCM3`;
  axioms standard. VERIFIED.
- run_heavy13 (build_heavy.sh): 0 errors, 21 axioms lines, none with sorryAx; `fibreQMPeriod_periodMap` now takes
  `S8WeightExact` instead of `S8Weight8`, `S8OrderCM3`. VERIFIED.
- run_light_full4: `lake env lean scratch/period-map/PMLight.lean` (all light parts): see file.

## PiCMC ⇐ CMDescends (part_heavy.lean)
- New leaf candidate `CMDescends` (CM QM surfaces over ℂ are base changes of CM ones over ℚ̄, as QM pairs).
  Proved `pi_of_descends`, `piCMC_of : R1fpProps → R2fpProps → BaseChangeClassUnique → PiTwistC → CMDescends → PiCMC`.
  `fibreQMPeriod_periodMap` now takes `CMDescends` instead of `PiCMC`.
- run_heavy14: errors (AbVar namespace, `ιe 16`); fixed. run_heavy15: 0 errors, 22 axioms lines standard. VERIFIED.
- run_full1 (before PiCMC step): build_full.sh single file, 0 errors, 3m02s, 68 axioms lines, none sorryAx. VERIFIED.
- run_full2 (final): build_full.sh (FibreQM base + part_fqm + part_light + part_theta + part_siegel + part_order +
  part_heavy), `lake env lean`: 0 errors, 3m13s, 69 axioms lines, none with sorryAx. VERIFIED.
- run_light_full5 (final PMLight.lean after docstring edits): 0 errors, 17 axioms lines standard. VERIFIED.
