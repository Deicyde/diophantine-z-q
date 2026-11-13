# period-glue results log

Task period-glue, 2026-11-13. Base: fork main 57a7fa26 + merge of origin/wip/period-map.

## SphereFactorAffine (gen_sphere.lean, part_sphere.lean; build_light.sh)
- Statement: period-map `part_light.lean` `PeriodMap.SphereFactorAffine` (used directly from the owner file; no copy).
- Generic lemmas (Mathlib only), compiled:
  - `descent`: F, H analytic on open O, F nowhere locally constant, G∘F = H on O ⇒ F''O open, G differentiable on F''O
    (open mapping for continuity; inverse function theorem off F''{F'=0}, countable by isolated zeros +
    hereditarily Lindelöf; `hasFPowerSeriesOnBall_of_differentiable_off_countable`).
  - `deriv_ne_zero_of_injOn`: injective analytic ⇒ g'(a) ≠ 0 (descent for g⁻¹, chain rule).
  - `affine_of_growth`: entire with ‖ψ z‖ ≤ C‖z‖ for ‖z‖ ≥ R ⇒ affine (Liouville on dslope ψ 0).
- P¹ part: `not_locally_const` (surjective holomorphic ℍ → P¹ is nowhere locally constant; clopen argument with the
  identity theorem in both charts), `sphereFactorAffine_proof : PeriodMap.SphereFactorAffine`,
  `hauptmodulUnique_of_S8 : PeriodMap.S8Nonzero → HauptmodulUnique`.
- run_light1: build_light.sh, 0 errors, 17 s; all axioms lines [propext, Classical.choice, Quot.sound]. VERIFIED.

## BaseChangeClassUnique (part_rigid.lean, part_bc.lean)
- part_rigid.lean: lines 16-183 of scratch/mul-rigidity/Rigidity.lean verbatim (generic `MulRigidity` namespace) + `end`.
  Compiles unchanged after FibreQM's `import Mathlib` base.
- `baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique` (statement used from period-map's part_heavy.lean,
  no copy): `IsPullback.isoIsPullback` gives e : Q.A ≅ Q'.A over Spec ℂ with e ≫ g' = g; `IsPullback.hom_ext` gives
  ι-equivariance and η(a) ↦ η'(a); at a = 0 (`toMul 0 = 1 = toUnit ≫ η`, `(toUnit ptObj).left = 𝟙`) the identity section
  is preserved, so e, e⁻¹ are homomorphisms by rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`).
- prereq: lake build of QMLattice/JHeight/HeightConstant OK; run_base1: period-map build_base.sh → olean/PMBase.olean, 0 errors, 2m50s.
- DevBC (import PMBase + period-map parts + part_rigid + part_bc): 0 errors, 53 s; axioms [propext, Classical.choice,
  Quot.sound]. VERIFIED.
