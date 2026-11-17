# Evidence follow-up for PR #2 — no proof changes

This is an **evidence-only** deliverable for fork PR #2, not a repaired proof or
broader arithmetic acceptance.

- Reviewed head: `3e01aa877cd7434fdc759fe7b6a9271de6deff2e`
- PR base: `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`
- Fork merge commit: `b6223977015d6f25baf613d0c88a5c83050f9c84` (recorded separately)
- Original mathematical source: `33483f751e6dcd3f91fb303969838aca33ad0458`

The full replacement export regenerated for this run checks out locally to
Lean **4.35.0**. It is 88,408,652 bytes with SHA-256
`4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa`, matching
`EXPORT_REPLAY_INPUT.json` on the head, and has all 41 explicitly selected roots in source order.

## Independent verification supplied

- a root-by-root review of all 41 declarations and all 16 definitions, with a
  source/application scope and remaining arithmetic obligations;
- fresh four-module compilation with only `propext`, `Quot.sound`, and
  `Classical.choice`;
- preparation of exactly 12 generated source inputs using manifest
  `5a828f5d4608b801f7016b7c387fae3ab78274f237c8077771b38d7bbadd20a0`;
- `lake check --from-export ... --paranoid`, whose process exited 0 and recorded
  acceptance by **Lean default**, **Lean paranoid**, **lean4lean**, **nanoda**, **con-leche**, and **con-ron**;
- finite/adverse controls, an audit-history protocol self-test, root-lockfile
  preservation and all nine dependency-revision checks;
- the complete export as `packet.ndjson.zip`. Its CRC was tested and its
  decompressed payload reproduces the hash above. The archive hash is
  `15e2f2fb5d5f26202ea22baa38dfce23bc84a8207c70d5ea2fed38f1d53d8244`.

The final validator also passed all nine dependency revisions and all 62 core
manifest entries. Full details are in `PR_GUIDE.md`,
`INDEPENDENT_STATEMENT_REVIEW.md`, `EVIDENCE_VALIDATION.json` and the retained
commands, outputs, metadata and logs in this evidence directory.

## Important limits

**No defective proof was found within the conditional local-interface scope.**
This isn't proof of the actual global boundary–cup/Poitou–Tate normalization,
common-strict/stored-row realization, determinant-basis compatibility,
retained-limit descent, restricted converse, or the main Diophantine theorem.

A working but conditional group-cohomology H¹ definition is not a continuous
Selmer object. These tests also are not a protected comparator challenge,
Open Math cloud execution, independent hermetic dependency rebuild, or external
specialist peer review. Fork-hosted Codex display and the unavailable Qodo review
are not counted as independent kernel evidence.

Required setup fixes (a separate `Cli` package compilation, metadata root/path
handling and dependency materialization, and timeout recovery) are documented
in `ENVIRONMENT_FIXES.md` and `METADATA_REPAIR_NOTES.md`. They changed no
mathematical source, expected outcome or historical result.

**Please review this as an evidence-only follow-up. It should not be
auto-merged.** The primary code/proof branch, frozen39 sources, original
receipts, manuscript and lockfile remain unmodified.
