# smooth-fibre report

**Main result: `SmoothFibreReduced` is proved**, from Mathlib only, with the standard axioms
(propext, Classical.choice, Quot.sound; `#print axioms` VERIFIED).

- `ZInQKernel/Contrib/SmoothFibre/Statement.lean`: `ZInQ.SmoothFibre.SmoothFibreReduced`, a
  verbatim copy of `VertWitness.SmoothFibreReduced` (scratch/vert-witness/VertWitness.lean:1840).
  Only the namespace differs, to avoid a clash with vert-witness. The bodies are identical, so the
  two are defeq.
- `ZInQKernel/Contrib/SmoothFibre/Basic.lean` (builds with `lake build ZInQKernel.Contrib.SmoothFibre.Basic`):
  - `theorem ZInQ.SmoothFibre.smoothFibreReduced : SmoothFibreReduced`
  - `theorem ZInQ.SmoothFibre.isReduced_of_smooth_of_field (k A) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] : IsReduced A`
  - `theorem ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain (P S) [CommRing P] [IsDomain P] [CommRing S] [Algebra P S] [Algebra.Etale P S] : IsReduced S`
- Route: Mathlib's local structure theorem says a smooth algebra is locally standard étale over
  `k[X_1..X_n]` (`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`). Étale over a domain
  embeds by flatness into an étale algebra over the fraction field, and that algebra is reduced
  (`Algebra.FormallyUnramified.isReduced_of_field`). Finally `A/mA ≃ R/m ⊗_R A`.
- Remaining: none. vert-witness can pass `ZInQ.SmoothFibre.smoothFibreReduced` as `hSR` (not
  compiled here, because that file is scratch).
- Docs: docs/research/smooth-fibre.md. Log: scratch/smooth-fibre/log.md. No vendored Tau Ceti code
  and no edits to existing files.
