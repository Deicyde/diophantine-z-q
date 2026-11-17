# Open Math OS handoff: PR #27, retained comparator evidence

**Preparation only. New comparator and paranoid execution: NOT_RUN.**
Execute this bounded request in Open Math OS, then return the retained artifacts
for local validation and integration into [PR #27](https://github.com/elliotglazer/diophantine-z-q/pull/27).
The request is for selected comparison/retention checks; it does not declare that
a whole release or critical assurance profile is complete.

## Fetch and freeze

- Repository: `https://github.com/CheyLoveday/diophantine-z-q.git`.
- Branch: `codex/upstream-local-boundary-interfaces-v13`. Use a clean checkout of the published handoff
  commit; record its full SHA and the trusted request/support manifest hashes.
- Mathematical baseline: `059bf903b441220246d5c1161f8dc24165b7a534`.
- Read [REQUEST.json](REQUEST.json), [SUPPORT.sha256](SUPPORT.sha256), the PR's
  existing specification/application map, and applicable repository instructions.
- Compare all trusted input hashes before execution. Freeze the challenge,
  comparator configuration, export list and manifests under the trusted operator's
  control; a solution build must not be able to rewrite them or its evidence sink.

Use the separate frozen challenge in research/local-boundary-interfaces/comparator/. Its 39 theorem holes and two homotopy-valued definition holes cover exactly the existing 41 roots. The 16 supporting declarations, including the two structures, stay fixed. Only the one intra-packet import is redirected to the challenge copy. Independent source review is recorded alongside this handoff; this is not protected controller acceptance.

The earlier source-bound six-checker export and receipts are preserved in ../openmath-os-evidence/. That root-only export lacks Nat.lor, Nat.xor, String.mk and semiOutParam, required by the comparator; regenerate from the same mathematical files with the full export list.

## Offline preparation

Run from the repository root, choosing a new output directory:

```sh
sha256sum -c docs/openmath/local-boundary-interfaces-v13/retained-comparator-20261110/SUPPORT.sha256
python3 -B scripts/prepare_local_boundary_comparator.py --output lean/.checks/pr27-retained-comparator
```

This runs Python and Git only: no Lean, dependency download, cloud dispatch or
checker. It checks the original frozen manifests and mathematical bytes, invokes
the unchanged original preparer, and adds comparator retention support.
`COMPARATOR_INPUTS.sha256` indexes the complete resulting input project.
`RETENTION_PREPARATION.json` binds the actual checkout and the base-stage identity.
For PR #27, `BASE_PROJECT_MANIFEST.sha256` and `SOURCES.json` describe the base
stage before adding the challenge/Lake root overlay; they do not index the whole
comparison project. The complete comparison index is authoritative for this run.

## Open Math OS execution

Use Linux with the pinned Lean **4.35.0** toolchain
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and the unchanged nine dependency
revisions, including Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Verify actual versions and locked checkouts rather than assuming the cache matches.
Use Open Math OS's normal job controls; retain its job/run identifier and actual
timeout, cancellation and durable-output configuration. No infrastructure or
resource quota is provisioned by this repository handoff.

1. Verify `COMPARATOR_INPUTS.sha256`. Retain this index, preparation receipt,
   original pin files, actual dependency revisions and cache provenance. A fresh
   project build may reuse the pinned dependency cache; do not describe it as a
   hermetic rebuild of all dependencies.
2. Build `Challenge` and `Packet` and export each **inside the supported
   Linux bubblewrap policy from the pinned Lake source**. Dependency resolution
   alone may use the network; build/export must have no network. Protect source,
   trusted challenge/configuration and result storage from the build. Export
   stdout must be streamed by the trusted operator to persistent files outside
   the build's writable paths. Record the actual sandbox command and grants.
   Use the bundled exporter, not an upgraded exporter. No sandbox bypass flag.
3. Both exports must use every line of `export-roots.txt` in order, not just the
   41 proof roots. It contains 74 explicit
   roots, including the standard comparator primitive/builtin declarations and
   permitted axioms. These extra bookkeeping roots add no mathematical claim.
   The logical exporter argv is `leanexport MODULE -- ROOT1 ROOT2 ...`; resolve
   its exact bundled path and `LEAN_PATH` in the pinned workspace. Export
   `Challenge` to `returned/challenge.ndjson` and `Packet` to
   `returned/solution.ndjson`. Keep stdout as raw NDJSON and stderr as a separate
   complete log, plus each argv, working directory and exit code. Check both
   source/input hashes again after build/export. **Do not use Lake's temporary
   internal export files as the only retained proof artifact.**
4. With both persistent exports present, run the comparator on these exact bytes
   from the generated project. Capture its own exit status and stdout/stderr:

```sh
lake comparator --config comparator.json \
  --challenge-from-export returned/challenge.ndjson \
  --solution-from-export returned/solution.ndjson --paranoid
```

Hash both exports immediately before and after this command; require equality.
No second `lake check --paranoid` campaign is needed. The comparator must report
matching theorem statements and fixed definitions, enforce only `propext`,
`Quot.sound`, `Classical.choice`, and accept the solution with all six checkers:
Lean default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron. Only the
challenge contains intentional `sorry` holes; solution `sorryAx`, custom axioms,
omitted roots or skipped/refusing checkers cannot count as success.

Supplying both exports avoids rebuilding them inside the comparator. That mode
does **not** itself establish a source-to-export relationship: the protected
build/export records and frozen-input identities above are essential.

If compilation, sandboxing, export or a checker fails, retain the failure and
return it. Do not edit mathematical sources, narrow the target list, change
assumptions, upgrade dependencies or replace the six-checker set to get a pass.

## Required durable return

Return one evidence-only commit or downloadable archive with this layout under
`docs/openmath/local-boundary-interfaces-v13/retained-comparator-20261110/returned/`:

| Artifact | Required content |
| --- | --- |
| `challenge.ndjson.zip`, `solution.ndjson.zip` | Each contains exactly the corresponding raw NDJSON file; preserve the exact bytes consumed by the comparator. Compress only after successful export and retain even when later checks fail. |
| `INPUTS/` | The complete small prepared input project, its `COMPARATOR_INPUTS.sha256`, `RETENTION_PREPARATION.json` and trusted request/config/export list. No dependency or build caches. |
| `commands.json` | Full actual argv, cwd, timestamps, stdout/stderr paths and exit code for preparation, dependency resolution/cache fetch, build, each export and comparator. Include sandbox argv, timeouts/cancellation and final job state. |
| `logs/` | Complete stdout/stderr for those commands, including all six comparator checker outcomes. |
| `TOOLS.json` | OS/architecture, Open Math OS job identity, Lean/Lake/exporter/comparator/bubblewrap identities, checker executable SHA-256 values and actual nine dependency revisions/cache provenance. |
| `RESULT.json` | The schema described below; report observed status and limitations. |
| `MANIFEST.sha256` | SHA-256 of every returned file except this index itself, paths relative to `returned/`. Include a concise failed-run index if the run is incomplete. |

`RESULT.json` must identify the exact PR/check-out, trusted request and support
index hashes, all mathematical input/pin hashes, config/export-list hashes,
prepared input index hash, build/export/comparator exit codes, target counts and
exact coverage. Record raw export byte counts and SHA-256 values, ZIP hashes,
the before/after export hashes, actual per-root transitive axiom sets (or exact
retained audit reference), comparator outcome, and **each** checker result/input
hash separately. Distinguish fresh observations from reused historical evidence.
Do not label missing artifacts/checks as passed. If no per-root axiom log is
regenerated, explicitly bind the unchanged historical audit and retain the new
comparator's transitive whitelist result; do not invent fresh per-root output.

Preserve failure attempts under separately named attempt directories. A summary
message, screenshots or an expiring job log cannot replace the exports and raw
receipts. Export compression should keep individual repository files below
GitHub's file limit; if needed, split the archive and retain the whole-export
hash plus reassembly instructions. Do not put plaintext secrets or caches in
the evidence. Keep the returned files durable before cleaning any job workspace.

## Local reception and PR finalisation

Locally verify archive integrity, raw and ZIP hashes, complete returned index,
all source/config/target/pin bindings, six checker outcomes and comparator exit
status. Compare mathematical source blobs against the baseline above. Update
this PR's existing evidence guide/description with the new receipts and exact
verified head; preserve older evidence and point-in-time statuses. Any new
paranoid execution needed to resolve a problem goes back to Open Math OS.
Protected controller acceptance and upstream merge remain separate decisions.

## Tooling basis

Command/export/sandbox semantics were checked on **10 November 2026** against
the installed Lean 4.35.0 source and the official
[4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/),
[pinned Lake checker source](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/CLI/Check.lean),
[comparison rules](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/Lake/Check/Compare.lean),
and [bubblewrap documentation](https://github.com/containers/bubblewrap/blob/main/README.md).
Lake's internal exports are temporary; supplied exports are not source-bound
automatically. Bubblewrap isolation depends on its actual command arguments,
so Open Math OS must supply and record the supported export sandbox rather
than treating a Linux job label as evidence of isolation. Platform quotas,
available memory and timeouts must be checked in the actual Open Math OS job;
they are not established by these offline preparations.
