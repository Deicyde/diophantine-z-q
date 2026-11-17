# Fork publication and Open Math handover

This is checking support for the bounded local-boundary PR in
**CheyLoveday/diophantine-z-q**. It adds no mathematical theorem and changes
none of the 65 files frozen at `43664fd17014018461d6dfd64cf052c1e4afe298`.
The core's earlier local-only status is a dated preparation record. On
2026-11-10 the owner authorized publication and integration into the fork;
this support and the PR description record the later stage separately.

Start with [HANDOVER.md](HANDOVER.md) for the exact Open Math OS task and
commands. The mathematical specification and application map remain in
`research/local-boundary-interfaces/`.

## Fresh local checks

- Four source modules compiled under Lean 4.35.0; all 41 proof roots passed
  their transitive axiom audit. The new elaborated statement output and four
  artifact hashes equal the previously reviewed core run. Exact commands and
  result: [native commands](native-commands.json), [native result](native-RESULT.json).
- The preparation script produced 12 byte-identical files in separate fresh
  directories, preserved all dependency revisions and refused an existing
  destination. [Validation record](LOCAL_VALIDATION.json).
- The generated Lake project built the four modules and its import-only Packet
  module. It emitted eight compatibility warnings because the unchanged legacy
  modules import Mathlib modules using the newer module system. There were no
  build errors; the generated config explicitly uses `requiresModuleSystem=false`.
  No source edit is hidden as a warning fix. Dependencies used existing caches.
- The exact 41-root export succeeded, with 88,408,652 bytes and SHA-256
  `4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa`.
  [Export command/receipt](EXPORT.json). The large export is retained locally
  under the ignored generated project, not added to the Git diff. Open Math
  must produce and retain its own source-bound export.
- Bundled native Lean 4.35 `leanchecker --silent --from-export` accepted that
  export with exit0 and empty stdout/stderr. [Native replay](NATIVE_REPLAY.json).
  This is the named roots and their transitive proof closure, not an unrelated
  default target. It strengthens the historical core's native-build evidence;
  it does not rewrite its point-in-time `NOT_RUN` replay status.
- Focused finite controls and the existing audit-history self-test passed again;
  [command receipts](LOCAL_COMMANDS.json) and complete output are alongside.

One local orchestration attempt used the wrong working directory for cache
setup and was stopped after dependency resolution began. Its partial directory
was retained; correctly rooted fresh preparation/build passed afterward.
This was not a proof or generator defect. The validation record preserves the
distinction. No required result is inferred from that interrupted attempt.

## Evidence and limits

The support manifest covers this directory and the preparation script, excluding
itself and the final support-review attestations to avoid self-reference.
Those attestations bind the completed manifest; Git binds all files. The
separate frozen core manifest and acceptance bindings remain unchanged.

These are local macOS checks with declared dependency-cache trust. Paranoid
checking, the five additional bundled checkers, the Open Math statement/source
review and its evidence PR remain pending. No protected comparator challenge
is supplied or claimed. The earlier frozen39 evidence is not evidence for this
41-root packet. A fork merge records integration, not arithmetic acceptance or
completion of the cloud run.

The broader arithmetic bridge, determinant normalization, parked four-term
proposal and research bank stay outside this PR. Only the selected four-module
interfaces, their evidence and the requested cloud handover are included.
