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
