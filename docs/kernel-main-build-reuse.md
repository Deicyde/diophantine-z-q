# Verified main build reuse: implementation and validation

The workflow implementation is described in [Verified reuse of main build
outputs](kernel-verified-reuse.md). It replaces the old project-output cache
with authenticated artifacts from successful exact-main runs. Compilation
reuse does not replace the complete kernel replay, exact-target checks or axiom
closure. Dependency setup still uses the pinned Mathlib cache.

## Code and trust boundaries

- `kernel_build_source.py` selects a producer from GitHub metadata, checking
  main ancestry, the approved workflow, exact successful attempt, job and
  artifact. `kernel_build_download.py` checks GitHub's archive digest, limits
  the download and removes the API token before following the signed redirect.
  Only these trusted selection operations receive a GitHub read token.
- `kernel_build_manifest.py` validates the complete archive, output sizes and
  hashes, module ownership and dependency closure. It rejects unsafe paths,
  links, duplicate entries, unknown outputs and incomplete modules. Candidate
  metadata cannot supply producer authority.
- The context, package, environment, runtime, resolution and inventory helpers
  fingerprint the installed compiler, dependencies, build controls and actual
  module lookup. Lean parses import headers. They reject missing or changed
  inputs and inconsistent source resolution. Candidate configuration executes
  without the selection token or provider credentials.
- `kernel_build_restore.py` stages verified files into absent project build
  roots. It does not replace dependency outputs. Invalid or incompatible
  evidence selects a cold build. An error after restoration begins stops the
  job; it does not continue with a partial installation.
- The driver and session helpers capture inputs again after the build and full
  audit. Lake runs with `--rehash` and separate controls that disable other
  artifact restoration. Only an exact-main push or dispatch can stage a
  reusable bundle after the complete audit passes with stable inputs and
  outputs. Consumers require the producer run to finish successfully.

The workflow reads the driver from protected main before candidate execution.
Until the driver is installed there, implementation PRs build cold. This is
intentional and does not demonstrate a production artifact restore.

## Measurements obtained

The [Linux validation run 44104869076](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44104869076)
used the actual compiler, context collector, verifier, restorer and unchanged
auditor on a four-module fixture. Cold, unchanged reuse and a one-module edit
produced equal complete audit reports covering five declarations. Unchanged
reuse restored all four modules; the edit restored only the independent
module and rebuilt the changed module's three-module reverse dependency
closure. Build times were 0.984s, 0.178s and 0.779s. Each full audit took about
2.4s; context preparation took about 21s per case. These are fixture results,
not a whole-project performance forecast or authenticated main-producer test.

The [full cold run 44104869120](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44104869120)
passed on PR157 head `18fe2c8fe6573ff078641b808819c1b0f7386cc1`, checked through
its test merge `47e7dd2de5c87292dbb3d121008b580923320d23`. It covered all 944
project modules, 37,708 declarations and 37,851 raw declaration occurrences.
Build commands took 57m52.068s and the full audit 22m14.326s. The additional
24 GiB swap was verified, about 27 GiB total. Root-build GNU time maximum RSS
was 11.98 GiB; audit maximum RSS was 14.09 GiB. Sampled audit process-tree swap
peaked at 7.80 GiB. Minimum available host memory during the root build was
2.06 GiB. RSS is not aggregate physical memory and tree sums can double-count
shared mappings. The original build and audit artifacts retain the samples.

## Remaining deployment validation

The current-main integration requires its own checks and review. After an
accepted implementation reaches main, measure the first cold main producer,
an unchanged PR restore and a one-module edit. Verify the independent GitHub
producer identity and artifact digest, compare the full audit reports and
report restored/rebuilt modules, transfer and hashing time, build and audit
time, host available memory, RSS, swap and disk usage. A local fixture or the
completed cold run does not supply those production measurements.

Tests must continue to reject forged artifacts and traces, forks, stale or
failed attempts, changed toolchains/dependencies, unsafe archives and partial
restores. Run the isolated reuse tests with
`python -B -m unittest discover -s scripts -p 'test_kernel_build_*.py' -v`.
Chained compilation and partitioned auditing are separate planned work.
