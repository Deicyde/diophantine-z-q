# Cloud batch 3, worker 12: port of the Anthropic FLT scheme-quotient proofs

This directory contains a port of theorem/proof pairs of the Lean development
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem) at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (files `Theorems/Thm_<name>.lean` and
`P2M/Sol/S_<name>.lean`), from that project's Lean v4.33.1 / Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` to this repository's Lean v4.35.0 / Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

- Copyright 2026 Anthropic, PBC.
- Apache License, Version 2.0: reproduced verbatim in `LICENSE`.
- The original project notice is reproduced verbatim in `NOTICE`, and its per-file third-party
  attribution in `ATTRIBUTION.md` (none of the files ported here is listed there: they contain no
  third-party material identified by the source project).

## Prominent modification notice (2026-11-16)

Every ported file is modified, and says so in a NOTICE OF MODIFICATION at its head, listing each
change. The changes are mechanical; no hypothesis or conclusion was weakened, strengthened or
omitted:

* the files were relocated under `ZInQKernel/Contrib/CloudB3W12FiniteQuotient/Vendor/AnthropicFLT/`
  (same file names), with imports retargeted, and each is wrapped in
  `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`, the
  isolation prefix of the existing FLT port `ZInQKernel/Contrib/CloudW03NeronSurj/`;
* the source's port-utility commands (`P2M/Util.lean`: `p2m_open`, `p2m_export`,
  `p2m_reactivate`, `p2m_exact_reverting`) are not used: they are replaced by Lean's own `open`
  command, plain declarations, and direct proof terms. The port defines no syntax, notation,
  macro, elaborator or other code that runs at build time;
* in Mathlib 56a, `CategoryTheory.Aut X` is a structure with the field `asIso`, so the source's
  `(ρ g).hom` is written `(ρ g).asIso.hom` (the same morphism), and the source lakefile's
  `leanOptions` are reproduced as file-level `set_option`s;
* individual proof repairs for Mathlib changes are listed in the file concerned.

The ported theorems (full names under the prefix above), each with its `P2MW.S_<file>.solution`:

* quotients by a finite group: `AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant`
  (the quotient of a scheme by a finite group whose orbits lie in invariant affine opens),
  `AlgebraicGeometry.Scheme.forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset`
  (invariant affine neighbourhoods on a separated scheme whose finite sets lie in affine opens) and
  `AlgebraicGeometry.Scheme.isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective`;
* quotients by a finite locally free equivalence relation:
  `RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation`,
  `AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation`,
  `AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback`,
  `AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation`,
  `AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict` and
  `AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`.

This notice describes provenance and changes, not a verification claim; the build logs, axiom
checks and `#discharges` output of the pull request that adds these files are the evidence.
