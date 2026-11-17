# Verification of the bounded four-module selection

Verification ID `LBI-V13-20261110`; date 2026-11-10. Profile: **development**,
with the owner's additional clean-checkout reproduction requirement. This is
native checking and model review of conditional interfaces, not release-profile
assurance, an arithmetic occurrence proof, or permission to publish.

## Snapshot and execution

- Preparation branch: `codex/local-boundary-interfaces-v13`, in a fresh worktree.
- Upstream base: `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`.
- Source selection: `33483f751e6dcd3f91fb303969838aca33ad0458` in the owner's fork.
- Foundation PR #15 observed head: `7c178b3edaf7f1ca9c91d542c3453bfdbaea73f3`.
- Four proof modules, 41 declared proof roots, 16 printed definitions; the root
  list includes two homotopy-valued definitions. [ORIGIN.json](ORIGIN.json)
  records original Git blobs and SHA-256 hashes, unchanged pin files and imports.
- Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib
  `56a005855ea17e0b0958f73ec801ae140b0a1679`; all nine package revisions match
  the unchanged `lean/lake-manifest.json` and have clean tracked source trees.
- Execution: macOS arm64. Exact Lean/Lake executable hashes, observed platform,
  per-root transitive axioms and fresh artifact hashes are in
  [native RESULT](evidence/native/RESULT.json).

The inputs were initially untracked additions in the fresh worktree. Each run
bound their actual bytes before/after; a base commit alone was not used as their
identity. All four mathematical sources remain identical to their original
research-commit blobs. A final commit and reviewable diff identify the assembled
package separately from the source commit.

Commands from the repository root:

```sh
python3 -B research/local-boundary-interfaces/verify_native.py lean/.checks/lbi-native-reviewed-20261110
python -B research/local-boundary-interfaces/check_controls.py
python3 -B scripts/check_audit_history.py --self-test
```

The first argument to the native runner must name a new output directory.
[commands.json](evidence/native/commands.json) lists every actual Lean/Lake
invocation, relative working directory and exit code. Each compile used
`lean -j1 -Ddebug.skipKernelTC=false`. The runner set `LEAN_PATH` to fresh
project output plus pinned dependency caches, and unset `LEAN_SRC_PATH`.
No existing project `Research` artifact was on that path. Module stdout and
stderr are empty; the audit emits the reviewed statements and axiom sets.

The development profile trusts the existing dependency caches and Lean standard
library. The cache was reused from the source research checkout; the earlier
source runner records Mathlib master-cache acquisition, including the LowDegree
closure. This preparation checked package revisions and tracked-source
cleanliness, but did not reauthenticate or source-rebuild cached binaries.
There is no hermetic-build or independent dependency-replay claim.

## Evidence and review

| Requirement | Evidence and observed scope |
| --- | --- |
| Fresh four-module native build | [native commands](evidence/native/commands.json) and [result](evidence/native/RESULT.json): every subprocess exited 0, source hashes unchanged, four fresh `.olean` hashes recorded. Binary outputs remain local; readable receipts are included. |
| Elaborated statement review | [statement/definition output](evidence/native/axioms-and-statements.stdout.txt), [generated audit source](evidence/native/Audit.lean), and separately authored reports in [reviews/](reviews/). Universes are printed; notation/implicit applications stay readable, deep statement terms are not elided. Source and referenced Mathlib definitions were also read. |
| Transitive axioms | All 41 roots passed `collectAxioms` against exactly `propext`, `Quot.sound`, `Classical.choice`. No `sorryAx`, custom arithmetic axiom or native-evaluation trust escape was found. This does not independently replay cached imports. |
| Focused controls | [design](CHECK_DESIGN.md), [source provenance](CONTROLS_PROVENANCE.json), [results](evidence/controls.json), [command](evidence/controls-command.json). 64 nonzero cup-correction cases, 640 degreewise cone cases, 4,680 two-term homotopy cases, 128 crossed-cocycle equations and 256 coboundary-pullback checks; all designated adverse cases detected. These are finite algebraic diagnostics. |
| Separate control rerun | [reviewer receipt](reviews/CONTROLS_REPRODUCTION.json): Python 3.13.12 reproduced all substantive JSON fields from the author's Python 3.12.3 run. Both reject optimized Python. The version difference is disclosed, not treated as new mathematical evidence. |
| Existing protocol self-test | [receipt](evidence/protocol.json): historical and existing-application structural/adverse checks passed. This does not add a new mathematical acceptance to the historical register. |
| Final clean-checkout reproduction | [Clean receipt](evidence/clean/REPRODUCTION.json): fresh detached checkout of `0715d6bf23d63e552c68a1dced24a85d216fa9b7`, no preexisting project output, all three commands exited 0 and the tracked tree stayed clean. All 17 native receipt files and four fresh artifact hashes matched. Controls matched the independent reviewer's output byte for byte; their only difference from the author's output was Python-version metadata. |

Native verification was first run with a more verbose printer that hid deep
terms. A second fresh run used readable unelided statement printing and the
source-map wording accepted by review. Only the latter run is cited above.
No proof source changed between runs. Initial logs are retained locally; old
research/foundation receipts are unchanged and are not substituted here.
Command receipts normalize local executable/cwd paths for publication; they
disclose that normalization, retain executable/version identities and bind the
exact original receipts held outside this submission. Output bytes are unchanged.

The mathematical scope and source-application review are by distinct Codex
agents, not by the integrator claiming independent acceptance of its own note.
Reviewers read the actual source and rederived critical signs/hypotheses.
Their shared model family, workspace and dependencies permit correlated errors;
this is neither independent human specialist acceptance nor checker diversity.
See [FINDINGS.md](FINDINGS.md) for the dispositions and remaining inputs.

The clean checkout used the same pinned dependency cache and host, without
preexisting project outputs; it is a clean project reproduction, not operating
system isolation or a dependency rebuild. Its receipt gives the exact snapshot,
commands, timings, input hashes and all compared output hashes. Duplicate native
logs are represented by byte-equality checks against the full logs already in
`evidence/native`, rather than copied twice. Fresh local `.olean` outputs are
retained in the clean worktree and bound by hash. The initial overly strict
control-receipt byte comparison failed solely on interpreter metadata; the
[comparison note](evidence/clean/COMPARISON_NOTE.md) and original error preserve
that event and its exact resolution.

To reproduce this method, create a fresh checkout of the prepared commit,
provide only the unchanged pinned dependency packages and their compiled caches
under `lean/.lake/packages`, then run the three commands above with no existing
`lean/.checks/lbi-native-reviewed-20261110` directory. The reproducibility claim
is conditional on those disclosed cache inputs. The runner refuses to reuse an
existing project-output directory.

The earlier core review records the pre-clean-checkout state at `0715d6b`.
Its original report and bindings are preserved; later status edits do not
retroactively change that review. [FINAL_ASSEMBLY.md](reviews/FINAL_ASSEMBLY.md)
and its separate binding review the completed clean evidence, current status
prose, and final [MANIFEST.sha256](MANIFEST.sha256). All mathematical sources,
README/application, proof-root selection, runners and controls are unchanged
from the reviewed and reproduced snapshot. Only evidence/status packaging was
added afterward. The final Git commit additionally binds the two final-review
attestations, which are excluded from the manifest to avoid self-reference.

## Assurance gates and missing checks

| Gates | Status | Scope |
| --- | --- | --- |
| A01 scope/snapshot; A02 specification; A03 semantic review; A04 proof mapping | PASS | Exact four sources, explicit roots, application table and bound nonauthor source/statement reviews. |
| A05 build/lint; A06 axiom audit; A07 targeted boundaries | PASS | Native compilation without diagnostics, focused protocol self-test, transitive audit and reviewed adverse controls. No separate style linter is configured for these extracted Research modules. |
| A08 artifact replay; A09 protected frozen-statement comparison; A10 external checker | NOT_RUN | Not part of this declared development profile. Native compilation does not substitute for these stronger checks. No paranoid run or six-checker receipt is claimed. |
| A11 clean reproduction | PASS | Fresh project checkout and output, exact source snapshot, shared trusted dependency caches; no hermetic dependency rebuild or independent host. |
| A12 nonauthor mathematical review | PASS | Distinct model agents, with the review scope and correlated-error limitations above. |
| A13 evidence/claim discipline | PASS | Final source/evidence manifest and separate assembly review bind the complete local package; exclusions and unperformed checks remain explicit. |

Development profile: **MET** for the conditional interfaces and declared cache
trust. The owner's additional clean-project-reproduction gate is also met.
Repository-required hosted CI, including `Protocol / independent agent audit`,
has not run for a new PR because publication has not been authorized. Local
model reports do not create that hosted check or maintainer acceptance. If a PR
is later authorized, keep it draft until the repository's required checks and
review conditions are satisfied. The local package is complete for owner review;
publication, hosted acceptance and the wider arithmetic programme are separate.
