# Source reuse notice

The fifteen supporting Lean modules in this directory and the mathematical proof in `ZInQKernel/Contrib/OneProof/TYZThm21At31.lean` reuse the existing project implementation from revision `f597c34cd6f6a43e076138209c638c47978753f5`:

https://github.com/Deicyde/diophantine-z-q/tree/f597c34cd6f6a43e076138209c638c47978753f5/ZInQKernel/Contrib/OneProof/T21Proof

https://github.com/Deicyde/diophantine-z-q/blob/f597c34cd6f6a43e076138209c638c47978753f5/ZInQKernel/Contrib/OneProof/TYZThm21At31.lean

The original mathematical proof bodies, namespace and attribution are retained. Supporting imports are relocated from `ZInQKernel.Contrib.OneProof.T21Proof` to `ZInQKernel.Contrib.CloudB3SC7T21`. The entry gains only a closed wrapper named `ZInQ.Contrib.OneProof.TYZAtThree.hT21_proof` with the unchanged target type; provenance and current-module-path comments are updated without changing the mathematics.

`BaseChange.lean` retains an adaptation of Tau Ceti's `exists_semilocalHom_sum_tmul_eq`, a private lemma in `NumberTheory/NumberField/Global/Adeles/FiniteBaseChange.lean` at revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`. Copyright 2026 The Tau Ceti contributors; Apache License 2.0. The adaptation is the integral-components special case named `exists_semilocal_coeffs`. The complete original license is included as `LICENSE-TauCeti`, and the existing source/dependency notices remain applicable.

This is source reuse, not a claim to have invented the earlier proof. Its published source history is preserved. No new external proof dependency or license grant is introduced. Existing third-party notices and imported dependency licensing remain applicable; see the repository's unchanged `THIRD_PARTY_NOTICES.md` and dependency notices. No third-party paper or compiler source is copied into this contribution.

The original proof combines the actual adelic Brandt computation, class-group and roots-of-unity calculations, and rigorous analytic L-value enclosures with kernel-checked rational certificates. Validation of this relocated source must be freshly reported and must not be inferred from the earlier source report.

AI-assisted reuse and validation operated by Jack McCarthy. Private evidence bundle available to the maintainer.
