# Cloud Batch 3 Worker 13 source recovery

This directory contains supporting source for reconstructing the guard-free
Shimura good-reduction theorem. The initial recovery snapshot is **unbuilt**:
source recovery alone is not a proof or a discharge.

## Sources and credits

The principal reused source is Anthropic's Fermat's Last Theorem Lean development:

- Repository: https://github.com/anthropics/fermats-last-theorem
- Revision: `6e837e75355538c7f80bab5b956861e86c4eacc2`
- Copyright: 2026 Anthropic, PBC
- License: Apache License, Version 2.0 (`LICENSE`)
- Original third-party credits: `ATTRIBUTION.upstream.md`
- Original notice: `NOTICE.upstream`

The recovered source was previously ported by Cloud Batch 2 Worker 13, with
shared geometry providers from the other cloud workers. Original per-file
copyright, license, source-revision and modification notices are retained.
Existing kernel, Tau Ceti and other already-vendored modules are imported,
not copied or modified here.

## Additional modification notice

Cloud Batch 3 Worker 13, 2026-11-16, retargeted repository module paths into
`CloudB3W13` and `CloudB3W13Shared`, retaining the canonical mathematical
declaration namespaces. The initial snapshot intentionally excludes the old
custom `PortUtilExt` elaborators. Their callers and the missing compatibility
ports still require ordinary-source repairs before a build can pass.

The original D5 dictionary is missing and must be rederived. Later compatibility
repairs will be identified separately; an earlier recovered body is never
represented as the lost final body. No existing target statement or dependency
pin is changed. The toolchain is Lean 4.35.0 with Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The final contribution must be checked against the exact statement, have only
standard axioms, contain no prohibited build-time code, and report the actual
`#discharges` outcome. An H-119 proof alone does not directly prove the stronger
`SGRSplit.ShimuraIntegralModelRep` statement.
