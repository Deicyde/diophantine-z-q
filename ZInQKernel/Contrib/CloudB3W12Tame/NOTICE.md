# Cloud batch 3, worker 12: `HDec.MCRGlue.TameQuotientSmooth` (H-91)

This directory supports `ZInQKernel/Contrib/OneProof/TameQuotientSmooth.lean`
(`HDec.CloudB3W12Tame.tameQuotientSmooth_proof : HDec.MCRGlue.TameQuotientSmooth`). It contains two kinds of
material.

## Copies of the owner's task p1-quot3

`QuotProper.lean`, `TameInvariants.lean` and `TameQuotSmooth.lean` are copies of
`ZInQKernel/Contrib/OneProof/QuotientP1/{QuotProper,TameInvariants,TameQuotSmooth}.lean` from the branch
`wip/p1-quot3` of this repository (commit `b533b204d640ee45ac924ee030497d427ec9926e`; tasks p1-quot2 and
p1-quot3, reports `docs/research/p1-quot2.md` and `docs/research/p1-quot3.md` on that branch), under this
repository's licence. Changes, also stated at the head of each file:

* module paths moved under `ZInQKernel.Contrib.CloudB3W12Tame`, and every declaration namespace renamed
  (`HDec.MCRGlue.…` → `HDec.CloudB3W12Tame.…`) so that nothing clashes if p1-quot3's files are folded later;
* the one input of p1-quot3's proof that was not proved, the textbook field `CurveSplit.RegularSmoothPerfect`
  (Stacks 00TV), is removed: in `TameInvariants.lean` the perfect-field step `smooth_of_invariants_field` now
  proves smoothness of the invariant ring directly, because its local rings are normal of dimension at most one,
  hence fields (Mathlib `Algebra.FormallySmooth.of_perfectField`) or discrete valuation rings (the vendored FLT
  theorem below); `TameQuotSmooth.lean` drops the corresponding hypothesis and imports `TailW` instead of `TailR`.

## Vendored from the Anthropic FLT development

`Vendor/AnthropicFLT/{Theorems/Thm_,P2M/Sol/S_}Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_{isSeparable_residueField,perfectField}.lean`
are ported from [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem) at
commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (Copyright 2026 Anthropic, PBC; Apache License, Version 2.0,
reproduced in `Vendor/AnthropicFLT/LICENSE`; the project's `NOTICE` and `ATTRIBUTION.md` are reproduced
verbatim beside it; neither file ported here is listed in `ATTRIBUTION.md`). Prominent modification notice
(2026-11-16): each file is changed, mechanically, to build on Lean v4.35.0 / Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (the source builds on Lean v4.33.1 / Mathlib `db584cd6`), and lists its
changes in a NOTICE OF MODIFICATION at its head: imports retargeted, the file wrapped in
`namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end …` (the isolation prefix of the existing FLT port
`ZInQKernel/Contrib/CloudW03NeronSurj/`), the source's port-utility commands replaced by plain Lean (no syntax,
notation, macro, elaborator or other build-time code is defined), the source lakefile's options reproduced as
`set_option`s, and in the `isSeparable_residueField` solution file
`set_option backward.isDefEq.respectTransparency false` (a Lean 4.35 instance-search change). No hypothesis or
conclusion was weakened, strengthened or omitted.

This notice describes provenance and changes, not a verification claim; the build logs, axiom checks and
`#discharges` output of the pull request that adds these files are the evidence.
