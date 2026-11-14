# mcr-quot results log

Targets: the glue Props A `FibreAutTame`, B `GenericQuotientP1`, C1 `CMSectionsDisjoint`,
C2 `CoordinateFromSections` of `scratch/mcr-glue/MCRGlue.lean` (copied verbatim as the prefix of
`scratch/mcr-quot/MCRQuot.lean`).

## Step 0 (06:50, 2026-11-14) — VERIFIED
- `scratch/mcr-quot/MCRQuot.lean` = `scratch/mcr-glue/MCRGlue.lean` verbatim. Needs
  `lake build ZInQKernel.Contrib.Mobius.Main ZInQKernel.HDecomp.QM.Pin ZInQKernel.HDecomp.Descent.B2Glue`.
- `lake env lean scratch/mcr-quot/MCRQuot.lean`: exit 0, 23 s (compile0_out.txt).
- Tau Ceti / Contrib check: no quotient-by-group, P¹-scheme or fixed-locus piece in
  ZInQKernel/Contrib (directory listing + grep for ToP1/Möbius: only `ImagePlane.inv` (swap charts)
  and the Möbius rigidity of `Contrib/Mobius`). Mathlib 4.35 has the commutative-algebra core of
  quotients: `Algebra.IsInvariant`, `Algebra.IsInvariant.exists_smul_of_under_eq` (transitivity on
  primes), `Ideal.Quotient.stabilizerHom_surjective` (decomposition group onto residue
  automorphisms) in `Mathlib/RingTheory/Invariant/Basic.lean`.
- Computation (py/units.py, VERIFIED): all 72 classes of `(𝒪/3𝒪)^×` (coordinates in the basis
  `1, i, (1+j)/2, (i+k)/2`) contain a unit of `𝒪` (reduced norm ±1) with coordinates in [-3,3].
