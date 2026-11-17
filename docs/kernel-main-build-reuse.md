# Verified main build reuse: implementation in progress

No workflow uses this code yet. The existing main-only cache policy remains in
force. This branch begins option D1, the owner's requested reuse of verified
main compilation outputs in PR builds. It does not change the required audit.

`scripts/kernel_build_manifest.py` implements the first boundary. It validates
producer/run/attempt identity from independently obtained GitHub API records,
compares the approved workflow digest, and verifies the complete downloaded
archive digest before reading its manifest. The artifact's own claims cannot
replace any of those independent inputs. A successful exact-main run and its
successful exact-attempt kernel job are mandatory. Non-main branches, forks,
failed and interrupted producers are not eligible. Both main pushes and main
dispatches are supported:
the gate's own token merges start post-merge checks by dispatch. The source
commit must be an authenticated main ancestor, with the same approved workflow
digest. The independent API facts and the bundle bind the event and exact ref.

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

`scripts/kernel_build_source.py` now selects a producer using authenticated
GitHub metadata. It reads main's current tip, proves the producer's ancestry,
reads the producer workflow bytes, and checks the exact job and artifact.
Jobs and artifacts are fully paginated. A fresh run read rejects a retry that
starts during selection. The search examines at most ten recent successful
runs by default; an older eligible run omitted by this limit means a cold
build. The selector does not download or restore the artifact. Its JSON client
does not follow redirects or run candidate code. Workflow integration must run
the reviewed selector with a step-scoped read token before candidate execution.

`scripts/kernel_build_restore.py` stages only the selected modules after full
archive validation. It checks each staged file again, keeps its timestamp old
so Lake must check inputs, and then installs into absent project build roots.
Existing build roots, linked parents and missing local packages are refused.
If installing a second root fails, the first root is moved back before the
failure is returned. Dependency packages are never cleaned or overwritten.
The caller must not start candidate build processes during this operation.

## Work still required before a PR or deployment

1. Implement and validate the compiler-derived source inventory, package/config
   identity and source-resolution checks on the full baseline. A regex import
   approximation is insufficient. Keep candidate code away from the API lookup
   credential.
2. Integrate the metadata selector and a bounded artifact download, preserving
   the separation between trusted API credentials and candidate execution.
   Verify the complete archive against the independently obtained digest.
   Never take a candidate-supplied run ID as authority.
3. Produce the manifest and outputs only after a complete successful build and
   full audit. The first producer must be cold with the legacy project cache
   disabled. Only main publishes reusable artifacts.
4. Integrate verified staging with a clean checkout. Disable automatic Lake
   artifact-cache restoration and force content checks. An invalid bundle
   selects a cold build; an install/rollback failure stops the job rather than
   compiling with uncertain output state.
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
`python -B -m unittest discover -s scripts -p 'test_kernel_build_*.py' -v`.
