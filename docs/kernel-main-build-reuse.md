# Verified main build reuse: implementation in progress

No workflow uses this code yet. The existing main-only cache policy remains in
force. This branch begins option D1, the owner's requested reuse of verified
main compilation outputs in PR builds. It does not change the required audit.

`scripts/kernel_build_manifest.py` implements the first boundary. It validates
producer/run/attempt identity from independently obtained GitHub API records,
compares the approved workflow digest, and verifies the complete downloaded
archive digest before reading its manifest. The artifact's own claims cannot
replace any of those independent inputs. A successful main-push run and its
successful exact-attempt kernel job are mandatory. Branch, fork, dispatch,
failed and interrupted producers are not eligible.

Every output is checked against its SHA-256 and byte length. The archive must
contain exactly the manifest and declared regular files. Unsafe paths, links,
aliases, duplicate members/JSON keys, unknown files, missing files and incomplete
module outputs are rejected. Both root and local `lean/` package build paths are
covered. Each output belongs to precisely one module. This validation library
does not extract or install anything.

Reuse requires identical compiler/package environments and exact module input
records with an unchanged transitive project dependency closure. The graph
algorithm is iterative so a several-thousand-module chain does not hit Python's
recursion limit. A missing input or cyclic inventory is rejected; it is not
silently treated as an external dependency. The input records must be obtained
from the pinned compiler/Lake, including its import flags and resolved sources.

## Work still required before a PR or deployment

1. Implement and validate the compiler-derived source inventory, package/config
   identity and source-resolution checks on the full baseline. A regex import
   approximation is insufficient. Keep candidate code away from the API lookup
   credential.
2. Add the trusted API selector and ancestor check. Select only a successful
   main-push run of the reviewed workflow and an immutable artifact belonging
   to its exact attempt. Never take a candidate-supplied run ID as authority.
3. Produce the manifest and outputs only after a complete successful build and
   full audit. The first producer must be cold with the legacy project cache
   disabled. Only main publishes reusable artifacts.
4. Stage only selected, verified outputs through safe paths. Disable automatic
   Lake artifact-cache restoration and force content checks; do not let newly
   extracted timestamps grant an mtime-only shortcut. Failed validation takes
   the cold build path without leaving partially trusted outputs installed.
5. Integrate the workflow, contract pins, gate workflow pin, diagnostics and
   regression tests. Continue to replay every declaration, compare every exact
   target type and compute the full axiom closure on each run.
6. Run cold/warm hosted comparisons and adversarial tests, reporting actual
   reused/rebuilt modules, time, RSS, swap, disk, digest and transfer costs.

The local four-module experiment uses real Lean 4.35.0 outputs and rejects a
poisoned `.olean` before restoration. It shows selective reuse and invalidation
of an edited module's consumers with automatic Lake artifact caching disabled.
It does not establish GitHub provenance or full-project performance. The larger
measured plan, kept outside this branch until implementation is complete,
separately addresses chained jobs and the likely need for a lower-memory audit
reader/replay. Neither is implemented here.

Run the current isolated tests with
`python -B scripts/test_kernel_build_manifest.py -v`.
