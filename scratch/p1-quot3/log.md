# p1-quot3 results log

Base: wip/p1-quot3 = 19793c5d (p1-quot2). Merged origin/wip/dcy3-used (36240662, includes leaf-fold23: field
mumfordGroupLaw, DCY3Used.y3Connected_of_leaves) as 6abfc715 (clean).
Build tree: copy of ~/dzq-wt/p1-quot2/.lake/build and lean/.lake/build (19793c5d), then lake build of the merged tree.

## Findings
- VERIFIED (read): Mathlib `Algebra.Smooth.of_formallySmooth_fiber` (RingTheory/Smooth/Fiber.lean L238): flat + finitely
  presented + every fibre `I.Fiber S` formally smooth over `I.ResidueField` => smooth.
- VERIFIED (read): vendored FLT `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime`
  (CloudW03NeronSurj/Vendor/Theorems): smooth over a UFD domain => localizations at primes are normal domains.
- VERIFIED (read): Mathlib `Algebra.IsInvariant` (RingTheory/Invariant/Defs.lean), `Algebra.IsInvariant.isIntegral`.
- VERIFIED (read): chain textbook field `CurveSplit.RegularSmoothPerfect` (TailR L1471, Stacks 00TV, `<=` direction).
- VERIFIED (read): `ZariskiConn.ZariskiConnectedness` is already a kernel leaf (Contrib/ZariskiConn/Basic.lean).

## Compile log
- Build of the merged tree (DeligneComponentsY3Used, QuotientP1Printed): OK (6 min; TailZ23..TailZ40 rebuilt).
- scratch/p1-quot3/Invariants.lean (Mathlib only): `exists_algebraMap_mem_notMem` (norm trick), `localRingHom_injective`,
  `dvd_of_dvd_atPrime`, `isDomain_isIntegrallyClosed_atPrime` (normality of all localizations descends from C to
  D = C^G, finite G, no condition on |G|): compiles, 0 errors (VERIFIED).
- Invariants.lean extended: `smooth_of_invariants_field` (perfect field, C smooth of dim <= 1, D = C^G finite type
  => D smooth; uses the copied RegularSmoothPerfect and the vendored FLT normality of smooth algebras),
  `reynolds`, `exists_retraction`, `tensorAut`, `smooth_of_invariants` (R noetherian with perfect residue fields,
  B smooth over R with fibres of dim <= 1, |G| invertible in R, A = B^G of finite type => A smooth over R; flat as a
  retract of B, fibres by base change of invariants via the Reynolds operator, Mathlib
  `Algebra.Smooth.of_formallySmooth_fiber`): compiles, 0 errors (VERIFIED).
- Helper module ZInQKernel/Contrib/OneProof/QuotientP1/TameInvariants.lean generated from Invariants.lean (namespace
  QuotientP1Proof.TameQuot): `lake build` OK (VERIFIED). Added `perfectField_residueField`, the dimension lemmas
  `ringKrullDim_of_isStandardSmoothOfRelativeDimension`, `ringKrullDim_tensor_eq_one/le_one` (pullbackSpecIso and
  Contrib/Dim), `fibre_invariants`, `ringKrullDim_fibre_eq`.
- scratch/p1-quot3/Scheme.lean (imports TameInvariants and QuotProper): action of G on Γ(X, q⁻¹V) (`sect`, `action`),
  `invariant_setup`, `smooth_appLE`, `relDim_eq_one`, and
  `HDec.MCRGlue.TameQuotScheme.tameQuotientSmoothRelDim_of_regularSmoothPerfect : RegularSmoothPerfect →
  TameQuotientSmoothRelDim`: 0 errors; axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
  => Task part (1) done: TameQuotientSmoothRelDim proved from the chain's textbook field regularSmoothPerfect, no new leaf.
