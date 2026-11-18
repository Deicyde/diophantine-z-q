# Verified reuse of main build outputs

Compilation reuse does not reuse a proof verdict. Every required run still
builds the complete contract inventory, checks the frozen target, and replays
all project declarations with the unchanged kernel auditor.

The workflow first reads the reuse driver from the protected `main` branch.
It copies that code outside the candidate checkout before running candidate
code. Within the new reuse stages, only selection receives a GitHub read token.
Existing scope and base-report steps retain their separate read tokens. It checks the
producer's repository, main ancestry, exact workflow bytes, successful job and
run attempt, and GitHub's artifact digest. If the driver is not yet installed
on main, as during the first implementation PR, the job builds cold.

The old Actions project-cache restore and save steps are removed. This also
applies to main and to reserved dispatch refs. The initial main producer must
therefore compile without those old project outputs. Dependency setup remains
the existing pinned Mathlib cache operation.

After dependency setup, credential-free preparation checks the downloaded
bundle and fingerprints the installed compiler, dependency sources and objects,
build drivers, flags, module lookup and Linux runtime. Lean parses the import
headers. Only modules with unchanged source and complete dependency closures
can be restored, into absent project build directories. The build uses
`lake --rehash build`, so timestamps are not a substitute for input hashes.
Explicit per-run Lake controls disable other artifact restoration.

The seven known glibc shared objects under the compiler's `lib/glibc/` are
link inputs, as specified by [Lean 4.35.0's packaging script](https://github.com/leanprover/lean4/blob/v4.35.0/script/prepare-llvm-linux.sh#L54-L59).
They remain hashed and checked for changes, but are not tested as standalone
runtime libraries. Actual runtime selection of one of these objects is
rejected. This exception does not cover dependency libraries, other paths or
unknown files. All other loader errors still reject reuse.

A missing producer, invalid bundle or incompatible installed environment uses
the cold path, including malformed archives and native-query timeouts before
installation. An error after restoration starts fails the job rather than
continuing with a possibly partial installation. The decision and captured
inputs are kept in `kernel-reuse-evidence-<attempt>`.

Inputs are captured again after compilation and after the full audit. A main
bundle is staged only when those inputs, the build marker and the compiled
outputs remain unchanged and the full audit passes for that exact head and
inventory. Only an exact `refs/heads/main` push or manual dispatch can publish
`kernel-main-build-<run>-<attempt>`. Consumers require the completed successful
run, so an uploaded artifact from a later-failing job is not eligible.

The implementation's deployment validation must include Linux execution and
matching complete audit reports for a cold build, reuse of the same sources,
and a source change that rebuilds its reverse dependency closure. Report
download and hashing time, restored and rebuilt modules, total build and audit
time, peak memory, swap and disk usage. A local fixture or an offline test does
not by itself establish hosted performance or production acceptance.

Before deployment, the full-project candidate-driver validation is separate
from the required kernel check. It exercises the real package layout and
complete audit, then verifies a local restore without compilation. Its synthetic
identity and local bundle cannot authorize production reuse. See the
[validation description and limits](kernel-main-build-reuse.md).
