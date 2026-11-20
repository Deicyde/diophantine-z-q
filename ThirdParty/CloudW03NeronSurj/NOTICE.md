# Worker 3 H-76 source port: attribution and changes

This directory contains a selective port of the complete Néron-extension proof
closure from [`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`.

- Copyright 2026 Anthropic, PBC.
- Apache License, Version 2.0: reproduced verbatim in `LICENSE`.
- Original project notice: reproduced verbatim in `NOTICE`.
- Original per-file third-party attribution: reproduced verbatim in `ATTRIBUTION.md`.
  In particular, the depth material includes work from Imperial College London's FLT project,
  copyright 2025 Andrew Yang, with authors Andrew Yang, Kevin Buzzard, and Michael Rothgang.
  Mathlib copyright and author notices are retained through that attribution and the imported
  Mathlib files.

## Prominent modification notice (2026-11-14)

The original files in `Vendor/` have been relocated under this Contrib directory and their
project declarations isolated beneath `ZInQ.Contrib.CloudW03NeronSurj.FLT`. Imports and P2M
alias-command names were changed accordingly. Original diagnostics and unrelated elaboration
performance guards are not used as proof steps; fresh checks are recorded separately. The source proof closure has been ported from Lean 4.33.1/Mathlib v4.33.0 to the
repository's fixed Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Compatibility changes include explicit namespace/import repairs, 1-based `TFAE.out`
index updates selecting the same equivalence entries, and the backward-definitional-equality
and transparency options listed in the source files. These affect elaboration, not
kernel checking or the mathematical statements and hypotheses.

`Basic.lean` selects the source's bridge from `GrpObj` to its relative group law.
`Main.lean` supplies the source abelian-scheme property bundle from the kernel's existing
proper/smooth/geometrically-connected group object and bridges the restriction-map encoding.
It targets exactly `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` as fixed at
`cba8157f7d5d09a4a3c8462aba2f3245494a870e`, with no extra hypotheses.

The mathematical source is Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), §1.2 Prop. 8,
with the codimension-one properness argument and Weil's extension theorem (§4.4 Thm. 1).
The source proof implements those arguments rather than assuming a Néron mapping property.

This notice describes provenance and changes, not a claim of successful local compilation.
The completed proof's build log and axiom audit, if obtained, are the verification evidence.
