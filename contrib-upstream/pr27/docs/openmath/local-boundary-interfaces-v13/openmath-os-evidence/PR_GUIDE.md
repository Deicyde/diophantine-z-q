# Evidence guide for PR #2

## Submission identity

- Reviewed PR: **#2**, `Lean: local conjugation and boundary interfaces (41 roots)`.
- Reviewed head: `3e01aa877cd7434fdc759fe7b6a9271de6deff2e`.
- PR base: `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`.
- Fork merge commit: `b6223977015d6f25baf613d0c88a5c83050f9c84` — recorded separately, not used as the review checkout.
- Original research source: `33483f751e6dcd3f91fb303969838aca33ad0458`.
- Independently reviewed core snapshot: `43664fd17014018461d6dfd64cf052c1e4afe298`.
- Intended delivery: **evidence only**, with the four proofs, frozen39 packet,
  historical receipts, manuscript and dependency lockfiles preserved.

## Result

All requested layers completed in this Linux VM:

| Layer | Result and location |
| --- | --- |
| 41-root / 16-definition semantic and application review | **PASS within the conditional-interface scope.** [INDEPENDENT_STATEMENT_REVIEW.md](INDEPENDENT_STATEMENT_REVIEW.md) enumerates all roots and definitions, compares their actual hypotheses with the application map, and explicitly retains the remaining arithmetic obligations. |
| Independent native build and statement/axiom audit | **PASS.** All four modules and all 41 roots compiled; only `propext`, `Quot.sound`, `Classical.choice`. See `native-RESULT.json`, `native-commands.json`, `native-axioms-and-statements.*`, and `native-Audit.lean`. |
| Source-bound project and generation | **PASS.** The generated manifest is `5a828f5d4608b801f7016b7c387fae3ab78274f237c8077771b38d7bbadd20a0`. All 12 inputs pass SHA-256 verification. See `generated-manifest.*` and `INPUT_MANIFESTS.json`. |
| Output export | **PASS.** All 41 named roots, 88,408,652 bytes; bytes and digest verified below. |
| Six-kernel replay | **PASS on all six streams.** See `paranoid.stdout.txt`, `paranoid-exit-code.txt` and `ARTIFACTS_AND_TOOLS.json`. |
| Finite/adverse controls | **PASS.** See `controls.stdout.txt`, `controls.stderr.txt`, and `controls-optimized.*`. |
| Existing historical protocol self-test | **PASS.** See `protocol.stdout.txt`; no mathematical acceptance follows from this check. |
| Data/artifact/provenance validation | **PASS.** See `EVIDENCE_VALIDATION.json` and `validate_evidence.py`. |

No six-checker result is missing or unavailable in the final replay.

## Exact export accounting

There are **41 selected roots** in the exact order of `TARGETS.json`, not a
claim that the full exported closure consists of only 41 declarations. The
exporter was invoked as:

```sh
lake env leanexport Packet -- <the 41 roots in source order>
```

The fresh **88,408,652-byte** NDJSON has SHA-256
`4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa`, which
matches the supplied handover receipt. It cannot have been substituted by the
old file: that hash was computed again from the fresh bytes written by this
exporter. See `EXPORT_REPLAY_INPUT.json`, `packet.ndjson.zip` and `PACKET_ZIP.json`.

Because of its size, the archive is supplied as a 14,232,967-byte ZIP. The
single entry is `packet.ndjson`, exactly the original NDJSON content, not a
re-encoded or filtered declaration set. The archive has SHA-256
`15e2f2fb5d5f26202ea22baa38dfce23bc84a8207c70d5ea2fed38f1d53d8244` and passed
a ZIP CRC check plus decompression/byte-hash comparison. Independent validation
read-only validated the underlying export rather than trusting the archive
alone.

`lean4lean` reports 13,713 checked declarations. `con-leche` and `con-ron`
each report 13,716 accepted declarations. That larger transitive dependency
closure is expected, and does not contradict the selected root count of 41.

## Checker execution

The checker executes against the retained fresh export using:

```sh
lake check --from-export openmath-evidence/packet.ndjson --paranoid
```

Outcome recorded verbatim:

```text
Lean paranoid kernel accepts the solution
lean4lean kernel accepts the solution — checked 13713 declarations
nanoda kernel accepts the solution
con-leche kernel accepts the solution — accepted 13716 declarations (--verified)
con-ron kernel accepts the solution — accepted 13716 declarations (--verified)
Lean default kernel accepts the solution
Uses axioms: Quot.sound, propext, Classical.choice
```

`lake`/`lean`/`leanexport` are Lean **4.35.0**, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The replay used Lean's supported `lake check --from-export ... --paranoid`
interface, not a fictitious bare `lean --paranoid` command. It ran in this VM,
with sandboxing enabled and without `--inadvisably-no-sandbox`. Bubblewrap is
`0.11.1`; receipt: `bwrap-version.txt`.

`nanoda` is the checker selected by Lake, and the executable on this host is
named `nanoda_bin`. All protocol executables used for the replay are hashed in
`ARTIFACTS_AND_TOOLS.json`. This is a native export replay with multiple
checkers, not a protected challenge comparison, an Open Math cloud execution,
or a claim that an arbitrary supplied NDJSON export proves source statements.
The source-to-export binding is instead provided by the exact head, source
blobs, preparation manifest, build stream, root list and fresh export command.

`core-artifacts/` retains the four selected module `.olean` files. Sixteen
artifact records, and the eight protocol executable hashes, are retained in
`ARTIFACTS_AND_TOOLS.json`.

## Dependency/provenance accounting

All nine locked package revisions match exactly both the native driver and the
prepared project lockfile. The root `lean/lake-manifest.json` hash remains
`a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58`.
The 62-entry research core manifest hash remains
`ce59e6667e58c1858a0bb87830c35f4142dc1f69c805f2e4daaa169f130220e3`.
Mathlib remains `56a005855ea17e0b0958f73ec801ae140b0a1679`.

`PREPARED_DEPENDENCIES.json` records the final revision/source/cache checks.
`INPUT_MANIFESTS.json` additionally records the initial read-only links and the
separate source-rebuilt `Cli` package. The first operation interrupted a
checkout because the required `Cli` cache was not present, and that exact pinned
package was then rebuilt in the review workspace. Lake later materialized its
locked local dependency set and built the selected output from it. These are
not independent, end-to-end authenticated hermetic dependency rebuilds. The
four selected mathematical files retain the same source identities in all
cases.

## Exact application boundaries

This review supports the selected conditional deductions:

1. shared-unit conjugate cocycle transport including descent to real Mathlib H¹;
2. local cup/coboundary correction removed by a compatible closedness condition
   and chain trace;
3. preservation of the common global/local homology class by a supplied right
   homotopy inverse, including its cone-coordinate sign transport.

Out of scope remain: the actual global boundary–cup/Poitou–Tate argument,
orthogonal-comparison occurrence and inverse existence at every coefficient
regime, common-strict matrices and stored rows, integral determinant-basis
normalization, inner/outer limiting constructions, the restricted converse and
the main Diophantine theorem. Bounded group-cohomology realization is not a full
continuous Selmer model. Zero, divisibility and characteristic-two cases in the
algebra do not create a forbidden parameter inverse.

No new proof-root axiom of global Selmer duality or determinant preservation is
introduced. The declaration names are not evidence that all of those source
applications have been instantiated.

## Findings

**No defective proof was found within the declared four-source conditional scope.**
No proof bytes, controls, proofs' theorem statements or expected historical
results were changed in this review. Scope or assurance clarifications made in
earlier research packets are not subsumed as external validation in this
submission either. This is independent checking in the same VM, not an external
specialist peer review.

The environment required metadata/reproduction work which is disclosed in
`ENVIRONMENT_FIXES.md` and `METADATA_REPAIR_NOTES.md`. It included a missing
CLI cache, root-owned Git metadata, an interrupted package checkout, job
short-limits, and helper/path issues. Those are not mathematical failures and
are not advertised as successful first executions. The native proofs,
recorded export and the final six-kernel outputs themselves were obtained
without modifying a mathematical theorem or turning off a kernel check.

No hosted-check result is reported here as if it were a GitHub-hosted CI proof
or acceptance. PR #2's Qodo comment reported review unavailability because its
subscription was inactive; that offered no useful formal-check verdict. The
fork's separate Codex display is likewise not counted as independent kernel
verification. The completed raw local checker outputs, not that display, are
the evidence supplied here.

## File map

- **Claim/source review:** `INDEPENDENT_STATEMENT_REVIEW.md`.
- **Execution ledger:** `EVIDENCE_VALIDATION.json`, `native-RESULT.json`,
  `native-commands.json`, `EXPORT_REPLAY_INPUT.json`, `ARTIFACTS_AND_TOOLS.json`.
- **Exported closure:** `packet.ndjson.zip`, `PACKET_ZIP.json`.
- **Machine checks:** `native-Audit.lean`, `native-axioms-and-statements.*`,
  `paranoid.*`.
- **Controls:** `controls.*`, `controls-optimized.*`, `protocol.*`.
- **Inputs and pins:** `INPUT_MANIFESTS.json`, `PREPARED_DEPENDENCIES.json`,
  `SOURCES.json`, `roots.txt`, `TARGETS.json`, generated manifest inputs.
- **Operational preservation:** `ENVIRONMENT_FIXES.md`, `METADATA_REPAIR_NOTES.md`,
  `initial-background-timeout.txt`, `initial-native-failure/`,
  `initial-plausible-build.stderr.txt`, `initial-plausible-checkout-job.txt`.
- **Reproduction helpers:** `prepare-dependencies.sh`, `paranoid-run.sh`,
  `collect_artifacts.py`, `validate_evidence.py`.

This is an evidence submission for future independent audit, not a merge request
to silently approve the wider arithmetic programme. The evidence PR should remain
unmerged until human/owner review and any repository-required hosted checks pass.
