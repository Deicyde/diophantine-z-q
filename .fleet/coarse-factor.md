# coarse-factor (fleet summary)

**Verdict: `CoarseFactor` is proved** from the leaf-form `CanonicalCoarseX6` (and from `R1R2fpRep`). Each is
already a hypothesis of the qm-glue theorem that consumes `CoarseFactor`, so no new leaf is needed. With
curve-split's `CurveBijIso` (proved), rows H-1 and H-43 no longer need `CoarseFactor` or `CurveBijIso`.

* Split: `coarseFactor_of : PairsLift → FactorThroughSurj → CoarseFactor`.
  * `PairsLift` says every QM pair over ℚ̄ has a level-3 structure up to isomorphism. It is derived from
    `CanonicalCoarseX6` and from `R1R2fpRep`.
  * Finding: `X6Props` alone does not give that the forgetful map is onto X(ℚ̄).
* `FactorThroughSurj` (AG glue: a morphism of proper smooth ℚ-curves that is constant on the ℚ̄-fibres of a
  morphism onto X(ℚ̄) factors through it) is **proved in Lean**: `CoarseFactorAG.factorThroughSurj`.
  * Method: take the scheme-theoretic image of (f, f'). Its projection to X is finite (Mathlib Stacks 0AH8)
    and bijective on ℚ̄-points, and is shown to be an isomorphism by a new algebraic criterion
    `bijective_of_points` together with curve-split's `bijective_of_unramifiedAt`.
* What compiles (`lake env lean`; only propext, Classical.choice, Quot.sound; 0 errors):
  * `scratch/coarse-factor/Reduction.lean`
  * `scratch/coarse-factor/Factor.lean`
  * `scratch/coarse-factor/CoarseFactor.lean`
  * `scratch/coarse-factor/Discharge.lean`, which is qm-glue's ModuliCompare.lean verbatim over the kernel's
    `TailK`, plus `r1r2fpRep_of_canonical''` (H-1) and `x6ConicModel_of_canonical''` (H-43) without
    `hF`/`hCB`.
* The cloud-worker connectedness and spreading-out modules supply no step.
* What remains: nothing for `CoarseFactor`. Integration into qm-glue's consumers is left to the integrator.
* Report: `docs/research/coarse-factor.md`; log: `scratch/coarse-factor/log.md`.
