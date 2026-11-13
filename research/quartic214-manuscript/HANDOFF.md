# Manuscript handoff — November 12, 2026

This edition adds a complete TeX/PDF presentation to the 214-variable family in public PR30. The original construction, mathematical source files and review records at commit `110cf72565be326fd567cd1a64a3b2e00213dcd1` remain unchanged. The arithmetic threshold remains ineffective.

This revision follows the automated Astra audit of manuscript commit `a8843cca75ff29d51aa7b288c80b8bdc3a1ca3bb`. Its two printed-formula findings and the related notation defects identified during repair review are repaired through [exact source corrections](SOURCE_CORRECTIONS_V1.json), without rewriting the frozen proof packets. The [correction application](../quartic214-manuscript-review/CORRECTION_APPLICATION.json) binds the original arguments, corrected receiving passages, downstream consumers and related-use review. The complete earlier audit is preserved in [the audit archive](../quartic214-manuscript-review/audits/astra-a8843cc-20261112/PR_COMMENT.md); the earlier manuscript reviews are preserved in [the historical record archive](../quartic214-manuscript-review/history/a8843cc/README.md). Their earlier verdicts are not refreshed into acceptance of this revision. Current independent decisions and remaining source-coverage limits are recorded separately. The current `--reviewed-artifacts` check requires acceptance of its explicitly limited repair and packaging scopes; it does not issue complete-proof, complete-inventory or protected-App acceptance.

The main result is the 214-variable theorem. Older 222-, 314-variable and other systems in the retained Version 16 foundation are inherited constructions, not alternative counts for this polynomial. The original parent proof and its exact source history are available in [the 214 proof package](../quartic214/README.md) and [its public review records](../quartic214-protocol-d-public/README.md). The Version 15 [source](../version15/snapshots/v15-222-004/manuscript/quartic_v15.tex), [handoff](../version15/CUMULATIVE-HANDOFF.md) and [review history](../version15/README.md) retain the earlier research and negative results at their original scope. The closed public stack remains cited by PR30; [PR23](https://github.com/elliotglazer/diophantine-z-q/pull/23) remains the separate durable evidence archive.

The complete current foundation is [Version 16](../../manuscripts/quartic_v16.tex), including the exact horizontal-lift normalization, corrected Gaudron–Rémond citations and the explicit Tao–Ziegler proof-adaptation wording. [The foundation transition](../quartic214-manuscript-review/FOUNDATION_TRANSITION.md) compares their actual 214 consumers; unchanged source hashes are not used to bypass these corrections. The [Version 16 handoff](../version16/CUMULATIVE-HANDOFF.md) preserves the received Fable audit and its limitations.

The operative height-averaging argument uses the published product construction, preserving the required multiplicity. The earlier quotient route is retained only as explicitly superseded history. The manuscript map identifies the exact current source passages and the complete retained foundation; a source filename or historical verdict is not substituted for a required derivation.

For the manuscript, run:

```sh
python3 -B research/quartic214-manuscript/assemble.py
python3 -B research/quartic214-manuscript/check_source_corrections.py
python3 -B research/quartic214-manuscript/build_pdf.py
```

The build record gives the actual engine and input hashes. To compare a fresh build with the committed PDF in the recorded environment, append `--check`. A different TeX installation may produce different PDF bytes; do not refresh the accepted PDF hash solely to hide that difference. Review changed outputs and obtain a fresh exact binding.

For the immutable original construction and audit records:

```sh
python3 -B research/quartic214/check_port.py
python3 -B research/quartic214-protocol-d-public/check_records.py --self-test --require-scoped-review
python3 -B scripts/check_audit_history.py --self-test
```

The manuscript has its own adaptation checker and source-to-PDF review, documented in [the review guide](../quartic214-manuscript-review/README.md). These checks do not establish arbitrary mathematical implications, an effective N0, a full numerical witness tuple, or protected-controller eligibility.

Publication is restricted to this public manuscript extension. Read back the final public head, PDF and manifest against their reviewed hashes. The protected `Protocol / independent agent audit` decision remains a separate required public acceptance step. Further mathematical or source changes reopen affected applications and manuscript bindings.
