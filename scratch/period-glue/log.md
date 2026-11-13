# period-glue results log

Task period-glue, 2026-11-13. Base 6f296292 + merge of origin/wip/period-map (already contained).
Targets: period-map's glue `S8Nonzero`, `S8WeightExact`, `SphereFactorAffine`,
`BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`; restate leaves `ValenceBoundGammaStar`,
`CMDescends`.

## Setup
- `build_base.sh`: `PGBase.lean` = fibre-qm-period FibreQM.lean lines 1-20634 + part_fqm.lean +
  period-map part_light/theta/siegel/order/heavy (verbatim; = period-map's DevHeavy without the
  import). `run_base1.txt`: 0 errors, 3m13s. VERIFIED.
- prereq `lake build ...QMLattice ...JHeight ...HeightConstant ...Objects`: OK 1m25s (`run_prereq.txt`).

## BaseChangeClassUnique — PROVED (VERIFIED, run_bcu.txt)
- `BCU.lean`: `PeriodGlue.baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique`.
  Axioms `[propext, Classical.choice, Quot.sound]`.
- Inputs: Mathlib only; rigidity `isMonHom_of_geometricallyIntegral` copied verbatim from
  scratch/mul-rigidity/Rigidity.lean (namespace renamed `PeriodGlue.MulRigidity`).
- Proof: comparison map from the pullback property; every compatibility checked after composing
  with `g'` (`eq_of_comp`); level clause at `a = 0` gives identity → identity; rigidity.

## QMTwistLattice — REDUCED (VERIFIED, run_qmtwist.txt)
- `QMTwist.lean`: `qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg) : QMTwistLattice`.
  Axioms standard.
- `T11aRiemannHom`: LEAF (textbook; T11a with `Hom A A'` for `End A`; Mumford §1 + GAGA,
  Birkenhake–Lange Prop. 1.2.1, UNVERIFIED locators). `t11aRiemannEnd_of_hom` proves the kernel's
  `T11aRiemannEnd` from it (so it is no stronger than needed beyond the Hom generalization).
- `QMLatticeTwistAlg`: GLUE, pure algebra (twist relation on QM lattices ⇔ `τ' ∈ Γ*τ`).

## PiTwistC — REDUCED (VERIFIED, run_pitwist.txt)
- `PiTwist.lean`: `piTwistC_of (h1 : R1fpProps) (h2 : R2fpProps) (hT : TwistOrbitFinite Y Φ)
  (hF : FibreTransferC Y π) : PiTwistC Y Φ π`. Axioms standard.
- `TwistOrbitFinite`: GLUE (moduli): twist relation on ℚ̄- and ℂ-points = orbits of a finite set
  of automorphisms of Y.
- `FibreTransferC`: GLUE (AG, Jacobson): fibres of π = G-orbits on ℚ̄-points ⇒ on ℂ-points, for Y
  proper smooth over ℚ. Finding: without the properness/smoothness hypotheses the transfer is false
  (Y = Spec ℂ has no ℚ̄-points), so they are part of the statement.
