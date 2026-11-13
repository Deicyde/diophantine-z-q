# Optional cache-backed Axiom bridge check

`.github/workflows/axiom-bridge.yml` is a **separate, optional engineering check**.
It does not edit or replace `autoform-verify`, the root default target, branch
protection, required-check settings, or any Astra/adversarial acceptance gate.
Failures remain visible; only the diagnostic artifact upload is non-blocking.
The workflow runs manually (`workflow_dispatch`) and on **any branch's** push or
pull request changing `scratch/axiom-bridge/**`, its workflow, or its trusted
`.github/axiom-cache.json` hash manifest.

## Owner setup: publish the already-verified cache

`axiom-cache-v1` is now public at
https://github.com/Deicyde/diophantine-z-q/releases/tag/axiom-cache-v1.
On 2026-11-13, all four assets (two parts, `SHA256SUMS`, and
`release-cache.json`) were uniquely present in state `uploaded`, with exact
local sizes and SHA-256 digests verified. The owner published the release;
this workflow change did not create or upload it. The creation command below
is retained as a reproducibility reference, not a command to rerun.
A missing release/asset or bad checksum fails the optional check; there is
**no cold Axiom build fallback**.

Cache source base and release target:
`48b5f075e5509678c84685f0d1ec53febd10b1e5`. This is the repository source base,
not a claim that the bridge/workflow changes are already in that commit.
Pins: Linux x86-64, Lean `v4.35.0` (commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, Mordell
`82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`.

**Owner-only command; shown for review, NOT executed:**

```bash
W=/home/jackmccarthy/axiom-bridge-work-120c9ff6
gh release create axiom-cache-v1 \
  "$W/cache-assets/axiom-cache-lean4.35.0-mathlib56a0058-stacksc496df0-mordell82a30cb.tar.zst.part-000" \
  "$W/cache-assets/axiom-cache-lean4.35.0-mathlib56a0058-stacksc496df0-mordell82a30cb.tar.zst.part-001" \
  "$W/cache-assets/SHA256SUMS" \
  --repo Deicyde/diophantine-z-q \
  --target 48b5f075e5509678c84685f0d1ec53febd10b1e5 \
  --title 'Axiom bridge cache v1 — Lean 4.35.0' \
  --notes 'Pinned Linux x86-64 Stacks/Mordell build outputs for the optional Axiom bridge. Trusted hashes and setup: .github/axiom-cache.json and scratch/axiom-bridge/CACHE.md. Source base: 48b5f075e5509678c84685f0d1ec53febd10b1e5.'
```

Do not upload the unsplit archive as well: each part is below GitHub's 2 GiB
release-asset limit. The owner's local `SHA256SUMS` must contain **all three**
entries below (whole archive and both parts). The workflow downloads that file
but compares it against the **committed** hashes; downloaded checksums alone
are never trusted. Publishing requires the owner's release permission; CI
uses only `github.token` with `contents: read`, scoped to the download step.
No extra secret, write token, network/security change, or human contact is needed.

## Trusted bytes and cache contents

Authoritative input: `$W/cache-assets/release-cache.json`; its repository, tag,
archive and part fields are copied unchanged into `.github/axiom-cache.json`.
That committed file adds the unpacked tar size, 30 GiB disk budget, source base,
and cache-manifest identity pins.

Archive basename:
`axiom-cache-lean4.35.0-mathlib56a0058-stacksc496df0-mordell82a30cb.tar.zst`.

- Whole concatenated archive: **2,439,572,970 bytes**, SHA-256
  `4f54433701085fcb631670ff72bff07cf26ab3d47420592b3df5488fe8af8a3a`.
- `.part-000`: **1,992,294,400 bytes**, SHA-256
  `ae4657e24c0da6995e014bbabb164a0ae26671080b18fcbd38b61e0122b2ae99`.
- `.part-001`: **447,278,570 bytes**, SHA-256
  `f365d710f828b1335032afe774b2d7fc24004bd9241d11e94795e19471c7bd78`.
- Decompressed tar stream: **8,581,591,040 bytes**.

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
regeneration-only `*.setup.json` compiler inputs: **39,192,013,063 bytes**
(39.192 GB decimal), not trace outputs. Do not trim C/IR or companion files to
save space: Lake can then invalidate the cache and attempt a costly rebuild.
The embedded manifest records 446 StacksCore modules, 12,312 StacksFrontier
modules, and 11 Mordell modules, along with pins and the original axiom report.

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

## Runner sequence and fail-closed behavior

1. **First step, before checkout or installation:** print `df -h /`, remove only
   unused SDK directories `/usr/share/dotnet`, `/usr/local/lib/android`,
   `/opt/ghc`, `/opt/hostedtoolcache/CodeQL`; if necessary also
   `/usr/local/.ghcup` and `/home/runner/.ghcup`. Print `df -h /` again and fail
   unless at least **32,212,254,720 bytes (30 GiB)** remain. These commands are
   for the ephemeral GitHub-hosted runner **only**; never run them on a shared
   devserver. Python, `gh`, and needed system tools are not removed.
2. Check out without persisted credentials. Validate the bridge pins against
   the trusted hash manifest. Install elan `v4.2.3` with the **same pinned URL
   and SHA-256 check as the existing `autoform-verify` installer**, then install
   Lean `leanprover/lean4:v4.35.0`.
3. From `scratch/axiom-bridge`, run `lake update`, recheck dependency pins, and
   `lake exe cache get` for Mathlib. No `||` source-build fallback. Download
   the two release parts and `SHA256SUMS` with the read-only token.
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
6. With `LEAN_NUM_THREADS=1`, run the existing compiler-slot measurement helper:

   ```bash
   /usr/bin/time -v -o ci-logs/bridge.time \
     python3 scripts/measure.py --jobs 1 --label ci-cache AxiomBridge
   set -euo pipefail
   /usr/bin/time -v -o ci-logs/axioms.time \
     lake env lean Check.lean | tee ci-logs/axioms.log
   python3 scripts/check_axiom_output.py ci-logs/axioms.log
   ```

   The checker requires the nine bridge theorem names and rejects dependencies
   other than `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is
   allowed. The slot helper limits actual compiler processes to one, not merely
   Lean worker threads. Use a fresh measurement label for local repeated runs.
7. Always print both GNU-time peak RSS values and final `df -h /`. The optional
   artifact step retains only small logs, timings, JSON reports and measurement
   samples for seven days. It never uploads cache assets, oleans, toolchain
   shadows, per-module artifacts, or the whole `.lake` tree.

The job is `ubuntu-latest`, `timeout-minutes: 45`, `contents: read`. Keep this
check optional in branch protection; this change does not configure required
settings. Cache availability failure is not permission to bypass the root's
existing required checks.

## Evidence and limits

Parent-provided verification of this **exact** cache: a fresh clone/restoration
caused **zero Axiom recompiles** and reproduced the **identical nine-theorem
axiom report**. This implementation did not repeat the 8.58 GB restore or run
any Lean/Lake/compiler on the shared devserver. The parent separately owns the
root-default-build isolation check.

Measured fresh repository allocation: **18,457,100,288 bytes**. Staged parts
occupy **2,439,577,600 allocated bytes**, for **20,896,677,888 bytes** before
adding Lean (about **3,195,072,512 bytes**). Their sum is about **24.09 GB**;
the 30 GiB initial guard leaves installation, extraction and filesystem
headroom, and deleting parts recovers their space afterward.

Measured peak RSS: one-compiler bridge **12.13 GiB**, imports-only **12.09 GiB**,
axiom audit **12.14 GiB**. These suggest feasibility, not a successful GitHub
runner test: the hosted runner must still have enough memory and the release
must exist. The cold dependency build used **four compiler processes**, took
**5 h 25 min**, and its largest individual compiler peaked at **16.8 GiB**;
it is unsuitable for this 45-minute optional workflow.

For a metadata-only local check (no Lean, downloads, or extraction):

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scratch/axiom-bridge/scripts/restore_cache.py \
  --metadata .github/axiom-cache.json --check-pins scratch/axiom-bridge
```

Implementation validation uses tiny synthetic archives in new temporary
directories under the owner's workspace, including bad hashes, malformed
metadata, unsafe paths/links, symlink destinations and successful streaming
part deletion. Production cache integrity and fresh-clone Lean evidence remain
the parent's results; release publication and an actual Actions run are still
owner follow-ups.
