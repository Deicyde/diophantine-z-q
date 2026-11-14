# smooth-fibre results log

- Statement: `VertWitness.SmoothFibreReduced` (scratch/vert-witness/VertWitness.lean:1840), copied
  verbatim as `ZInQ.SmoothFibre.SmoothFibreReduced` in ZInQKernel/Contrib/SmoothFibre/Statement.lean.
  Compiles (lake env lean, no output). VERIFIED.
- Mathlib 4.35 inventory (VERIFIED, read in .lake/packages/mathlib):
  - `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` (RingTheory/Unramified/LocalStructure.lean:391):
    smooth at p ⇒ ∃ f ∉ p, S_f standard étale over `MvPolynomial (Fin n) R`.
  - `Algebra.FormallyUnramified.isReduced_of_field` (RingTheory/Unramified/Field.lean:123):
    unramified + ess. finite type over a field ⇒ reduced.
  - `Algebra.Smooth.baseChange`, `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`.
  - `IsRegularLocalRing` exists but "regular local ⇒ domain" does not.
- Route: A smooth over field k; locally A_f étale over P = k[X_1..X_n]; A_f flat over P, so
  A_f ↪ Frac(P) ⊗_P A_f, which is étale over a field hence reduced; so A_f reduced; so A reduced.
- PROVED (VERIFIED, `lake build ZInQKernel.Contrib.SmoothFibre.Basic` succeeds, only
  module-system warnings; scratch/smooth-fibre/Axioms.lean):
  - `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain`, `ZInQ.SmoothFibre.isReduced_of_smooth_of_field`,
    `ZInQ.SmoothFibre.smoothFibreReduced : SmoothFibreReduced`.
  - `#print axioms`: [propext, Classical.choice, Quot.sound] for all three.
  - `SmoothFibreReduced` unfolds by `rfl` to the verbatim vert-witness body.
