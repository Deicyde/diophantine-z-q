# Optional cache-backed Axiom bridge check

`.github/workflows/axiom-bridge.yml` is a **separate, optional engineering check**.
It does not edit or replace `kernel-lean`, `research-checks`, the root default
target, `KERNEL_CONTRACT.json`, the kernel checker, branch protection,
required-check settings, or any Astra/adversarial acceptance gate. Failures
remain visible; only the diagnostic artifact upload is non-blocking. The
workflow runs manually (`workflow_dispatch`), on pull requests changing
`scratch/axiom-bridge/**`, its workflow, or its trusted `.github/axiom-cache.json`
hash manifest, and on pushes to `main` changing those paths. Pull-request
branches are therefore not checked twice (once for the push, once for the PR).

## Cache release and provenance

The workflow downloads release `axiom-cache-v1` of
[`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q/releases/tag/axiom-cache-v1).
That release mirrors, with the same asset names and bytes, the cache first
published and verified at
[`Deicyde/diophantine-z-q` release `axiom-cache-v1`](https://github.com/Deicyde/diophantine-z-q/releases/tag/axiom-cache-v1).

The trust root is the **committed** `.github/axiom-cache.json`, not anything
downloaded. Its `repository` is the upstream repository, and
`scripts/restore_cache.py` accepts no other repository. Its asset names, sizes,
part and whole-archive SHA-256s and embedded cache-manifest pins are unchanged
from the producer's metadata. The producer's own `release-cache.json` still
records `Deicyde/diophantine-z-q`; that is historical provenance, kept in the
committed metadata as `historical_origin` (repository, tag and producer source
commit) and not read by the helper. The producer source commit is in the fork's
history, not this repository's.

If the release or an asset is missing, or any checksum differs, the optional
check fails. There is **no cold Axiom build fallback**.

Pins: Linux x86-64, Lean `v4.35.0` (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, Mordell
`82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`.

## Trusted bytes and cache contents

Archive basename:
`axiom-cache-lean4.35.0-mathlib56a0058-stacksc496df0-mordell82a30cb.tar.zst`.
Each part is below GitHub's 2 GiB release-asset limit; the unsplit archive is
not a release asset.

- Whole concatenated archive: **2,439,572,970 bytes**, SHA-256
  `4f54433701085fcb631670ff72bff07cf26ab3d47420592b3df5488fe8af8a3a`.
- `.part-000`: **1,992,294,400 bytes**, SHA-256
  `ae4657e24c0da6995e014bbabb164a0ae26671080b18fcbd38b61e0122b2ae99`.
- `.part-001`: **447,278,570 bytes**, SHA-256
  `f365d710f828b1335032afe774b2d7fc24004bd9241d11e94795e19471c7bd78`.
- Decompressed tar stream: **8,581,591,040 bytes**.

The release's `SHA256SUMS` must contain exactly these three entries. The
workflow downloads it but compares it against the committed hashes; downloaded
checksums alone are never trusted. CI uses only `github.token` with
`contents: read`; no extra secret or write token is needed.

The only payload roots, relative to the bridge's `.lake/packages`, are:

```text
Stacks/.lake/build/**
Stacks/LICENSE
Mordell/.lake/build/**
Mordell/LICENSE
AXIOM-CACHE-MANIFEST.json
```

Structural parent directories are allowed; package source/config files are
not. The cache retains **all build outputs**, including C, IR, ordinary oleans,
olean companions, ileans, traces and hashes. The **only omission** is
regeneration-only `*.setup.json` compiler inputs (about 39.2 GB), not trace
outputs. Do not trim C/IR or companion files to save space: Lake can then
invalidate the cache and attempt a costly rebuild. The embedded manifest
records 446 StacksCore modules, 12,312 StacksFrontier modules and 11 Mordell
modules, along with the pins.

`restore_cache.py` checks asset basenames, sequential part names, sizes, each
part SHA-256, the concatenated whole SHA-256, and the release checksum list
against committed metadata. **The whole hash passes before extraction starts.**
It keeps the verified part descriptors open, streams their concatenation into
`zstd -d -c` and Python's tar reader, and never creates another compressed
archive or an unpacked tar file. It rejects traversal, absolute paths, links,
sparse/special files, duplicate names, symlinked destinations, hard-linked
files, and paths outside the allowlist. It bounds and checks the unpacked byte
count and validates embedded manifest pins. After successful extraction it
**deletes the downloaded parts**. On failure it stops, retains parts for
inspection, and may leave a partial destination; discard that disposable
runner/destination rather than building from it.

`scripts/test_restore_cache.py` exercises these guards on tiny synthetic
archives (no Lean, network or real cache bytes); the workflow runs it before installing Lean.

## Runner sequence and fail-closed behavior

1. **First step, before checkout or installation:** print `df -h /`, remove only
   unused SDK directories `/usr/share/dotnet`, `/usr/local/lib/android`,
   `/opt/ghc`, `/opt/hostedtoolcache/CodeQL`; if necessary also
   `/usr/local/.ghcup` and `/home/runner/.ghcup`. Print `df -h /` again and fail
   unless at least **32,212,254,720 bytes (30 GiB)** remain. These commands are
   for the ephemeral GitHub-hosted runner **only**; never run them on a shared
   machine. Python, `gh`, and needed system tools are not removed.
2. Check out without persisted credentials. Validate the bridge pins against
   the trusted hash manifest and run the helper tests. Install elan `v4.2.4`
   with the same pinned URL and SHA-256 check as `kernel-lean.yml`, then
   install Lean `leanprover/lean4:v4.35.0`.
3. From `scratch/axiom-bridge`, run `lake update`, recheck dependency pins, and
   `lake exe cache get` for Mathlib. No `||` source-build fallback. Download
   the two release parts and `SHA256SUMS` with the read-only token; the
   repository and tag are read from the validated committed metadata.
4. Verify and stream-restore into this bridge's `.lake/packages`, then remove
   the downloaded parts. Require sufficient remaining disk for the full
   unpacked tar budget before extracting.
5. Run a **no-build** preflight over the three imported Mordell modules:

   ```bash
   lake --no-cache --no-build --fail-fast build \
     +Mordell.Jacobian.Existence +Mordell.Jacobian.Dimension \
     +Mordell.AbelianVariety.GoodReduction
   ```

   `+module` selects Lean artifacts and their dependency closure. Missing or
   stale outputs fail immediately; no unconditional Mordell/Stacks umbrella
   build, `lake clean`, or cold Axiom rebuild is permitted. Changing pins
   requires a separately regenerated and verified cache, not relaxed guards.
6. With `LEAN_NUM_THREADS=1`, build with one compiler process and audit:

   ```bash
   /usr/bin/time -v -o ci-logs/bridge.time \
     python3 scripts/measure.py --jobs 1 --label ci-cache AxiomBridge
   /usr/bin/time -v -o ci-logs/axioms.time \
     lake env lean Check.lean | tee ci-logs/axioms.log
   python3 scripts/check_axiom_output.py ci-logs/axioms.log
   ```

   The build compiles `ZInQKernel.HDecomp.Objects` (root package, Mathlib-only
   imports) and the bridge modules. The checker requires the nine bridge
   theorem names and rejects dependencies other than `propext`,
   `Classical.choice` and `Quot.sound`; no `sorryAx` is allowed.
7. Always print both GNU-time peak RSS values and final `df -h /`. The optional
   artifact step retains only small logs, timings, JSON reports and measurement
   samples for seven days. It never uploads cache assets, oleans, toolchain
   shadows, per-module artifacts, or the whole `.lake` tree.

The job is `ubuntu-latest`, `timeout-minutes: 45`, `contents: read`. Keep this
check optional in branch protection. Cache availability failure is not
permission to bypass the root's existing required checks.

## Evidence and limits

Cache-backed GitHub CI for the original bridge (which imported the scratch
`Leaves` module in the fork) passed with these exact cache bytes:
[pull request run](https://github.com/Deicyde/diophantine-z-q/actions/runs/43377672455)
and [push run](https://github.com/Deicyde/diophantine-z-q/actions/runs/43377666256).
Both verified the cache hashes, recompiled zero Axiom modules and passed all nine
axiom reports.

For this upstream package, a local Linux x86-64 check used a byte copy of the two
parts and `SHA256SUMS` with the committed upstream metadata:

| Step | Result |
| --- | --- |
| Verify + stream restore | 195,838 entries, 8,581,591,040 tar bytes, parts deleted; 2 min 11 s, 0.37 GiB RSS |
| No-build preflight | all 21,816 jobs up to date; 26 s |
| Fresh bridge build, one compiler | 5 modules (`ZInQKernel.HDecomp.Objects` + 4 bridge); **0** StacksCore/StacksFrontier/Mordell; 1 min 4 s; peak compiler RSS 12.09 GiB |
| `Check.lean` audit | all nine theorems, only `propext`, `Classical.choice`, `Quot.sound`; 8 s, 12.08 GiB RSS |

The published upstream release assets were then downloaded anonymously from
`https://github.com/elliotglazer/diophantine-z-q/releases/download/axiom-cache-v1/`
and passed the same verification and restore (identical `SHA256SUMS`, whole
hash, 195,838 entries, identical embedded manifest). A GitHub-hosted run of
this workflow is the remaining check.

The cold dependency build (four compiler processes) took **5 h 25 min**, and its
largest individual compiler peaked at **16.8 GiB**; it is unsuitable for this
45-minute optional workflow.

For a metadata-only local check (no Lean, downloads, or extraction):

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scratch/axiom-bridge/scripts/restore_cache.py \
  --metadata .github/axiom-cache.json --check-pins scratch/axiom-bridge
PYTHONDONTWRITEBYTECODE=1 python3 scratch/axiom-bridge/scripts/test_restore_cache.py
```

These are scoped build and axiom checks, not acceptance of any manuscript
argument.
