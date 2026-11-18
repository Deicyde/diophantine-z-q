# Local wild-inertia supporting results

This checkpoint proves supporting local-Galois, Tate-module and smooth-group results on the original objects. It does **not** prove `SZRaynaud.ElliotWildInertiaTrivial` or the full Z-in-Q statement, and it changes no assembly hypothesis.

## Closed results

- `OriginalWildTateImage.original_rational_wild_image_finite`: the actual wild-inertia image on `A.V ℓ`, under the original `A.galRep ℓ`, is finite when ℓ is a unit at the number-field valuation. The corresponding integral result works over any original algebraic closure. Finiteness is not triviality.
- `OriginalWildTateImage.original_tate_basis` and `OriginalTateLatticeContinuity`: construct a finite-free original Tate lattice and a continuous Galois matrix action from the finite first-projection image. No rank, basis, whole-torsion projection surjectivity, or geometric degree formula is supplied. The rank is not identified with twice the dimension.
- `ActualNumberFieldDivision.genuine_division_factor`: constructs the actual finite Galois division field, faithful action on all original prime-power torsion, continuous surjective restriction and exact factoring equation. `ActualNumberFieldQuotient` supplies the actual finite continuous quotient. Level zero is included.
- `ActualTameInertia.leaf_tame_generator`: constructs one actual inertia element that generates inertia modulo globally strict wild automorphisms on every finite Galois layer. No inertia-restriction surjectivity, henselianity, or supplied generator is assumed.
- `FrobLift.exists_frobenius_lift`: constructs a Frobenius lift over the original number-field DVR. Its conjugation relation is modulo the actual wild subgroup, not an exact operator relation on every Tate vector.
- `HenselDivision.SmoothCommMulEtale.multiplication_etale_of_smooth_comm`: multiplication by an invertible integer is étale on any smooth commutative group scheme over a commutative ring. Properness and connectedness are not required.
- `HenselDivision.henselianLocalRing_of_isAlgClosed`, `isAlgClosed_residueField` and `ValuationTorsionV001`: derive strict-henselian properties of any valuation subring of an algebraically closed field and torsion specialization/lifting over it. The valuation ring is not assumed discrete, Noetherian or finite over the base.

Older conditional division-field and counting lemmas are retained exactly as stated. Their hypotheses are not retrospectively removed. The closed endpoints derive the finite torsion, basis and residue-prime inputs they need.

## Verification and remaining scope

The 83 source modules and 527 distinct named declarations have independent mathematical source review and ordinary Lean compilation, with complete standard-axiom audits. Verification uses Lean 4.35.0, Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, and disclosed reused import objects. It is not a clean from-scratch build.

All 56 reachable project dependency sources for the Tate-image endpoint were checked byte-identical to this work-in-progress checkout. The new modules are additive and preserve the reviewed proof bodies.

Still required: original Néron-model/Tate comparison, non-integral toric directions, the monodromy/annihilator geometry, and the exact unrestricted wild-inertia conclusion. The smooth-group and valuation-ring theorems do not assert that every geometric torsion point extends integrally. No main-branch integration is claimed here.
