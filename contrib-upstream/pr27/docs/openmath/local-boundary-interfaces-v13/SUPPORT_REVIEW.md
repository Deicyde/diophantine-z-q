# Review of publication and Open Math support

Date: 2026-11-10. Reviewer: Codex `/root/normalization_claim_review`.
The reviewer did not author the preparation generator, handover or local
execution receipts. This is a bounded nonauthor model review of support and
provenance, not another arithmetic investigation or independent kernel
implementation. Shared model, host, toolchain and source limitations remain.

**Decision: PASS for the support's stated scope.** It prepares the exact
four-module / 41-root selection for source-bound cloud replay and preserves
the frozen core. Its handover correctly targets the owner's fork
`CheyLoveday/diophantine-z-q:main`; it does not request another upstream PR.
The later publication authorization is separated from the core's historical
local-preparation record. This review makes no cloud-pass or merge-status claim.

## Generator and isolated project

I read the complete generator and independently ran it once into a new
temporary project. Its 12 files reproduced the recorded generated manifest
`5a828f5d4608b801f7016b7c387fae3ab78274f237c8077771b38d7bbadd20a0`.
All 11 manifest entries matched. The four Lean sources are byte-identical to
the selected core sources; the only lockfile change is the root package name,
with all nine dependency records unchanged. `roots.txt` exactly matches the
41 distinct frozen proof roots and `Packet.lean` contains only the four imports.

The generated Lake configuration selects `LocalBoundary`, explicitly includes
Packet and all four modules, and supplies `-Ddebug.skipKernelTC=false`.
The explicit legacy-module setting changes build support, not proof source.
Repeating preparation at the existing destination exited 1 and changed none
of its files. The generator performs no installation, Lean run or cloud dispatch.
I did not repeat the integrator's Lake build or checker run.

One handover finding was resolved: Python `assert` guards on the root list
were replaced by explicit conditional failures, so optimized Python cannot
erase those guards. No generator or mathematical-source correction was needed.

## Command semantics and claim boundary

I checked installed Lean 4.35 help and the exact toolchain sources
`LeanExport.lean`, `LeanExport/Basic.lean` and `lake/Lake/CLI/Check.lean`.
The exporter argument order is `leanexport MODULE -- ROOTS...`; a supplied
root list exports those declarations with their dependencies. The installed
`lake check --from-export FILE --paranoid` path checks that supplied export,
skipping source build/export. Its bundled set is Lean default plus Lean
paranoid, lean4lean, nanoda, con-leche and con-ron. The normal command requires
Linux/bubblewrap. The [official Lean 4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/#checking-projects-with-lake-check-and-lake-comparator),
checked on this date, agree with these interfaces.

The handover correctly requires separate source-to-export provenance and
statement/application review. `--from-export` alone cannot certify origin in
the repository, and no protected comparator challenge is supplied. Manual
build/export uses the isolation provided by Open Math, which the operator
must record; `--paranoid` is not a blanket isolation claim for earlier steps.
Missing or skipped checkers are not accepted as passes. The plan retains exact
exports, commands, streams, hashes and unsuccessful attempts, and forbids
silently upgrading dependencies or disabling checking to obtain success.

## Local receipts and artifact inspection

The new direct native run's statements, selected root/axiom lists and four
artifact hashes match the reviewed core. Its 12 before/after input hashes
match current files. I checked the actual local artifacts and the published
receipt copies. The generated Lake project's five artifact hashes also match
its separate record; these are separate build artifacts from the direct
native run, not claimed byte-identical to it.

The source-bound scoped export is 88,408,652 bytes with SHA-256
`4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa`.
I independently streamed and parsed all 1,677,955 NDJSON records, reconstructed
declaration names and found all 41 selected roots: 39 theorem declarations and
two definitions. Its serialized axioms are precisely `Quot.sound`, `propext`
and `Classical.choice`. This parsing checks inventory and provenance; it is
not another proof checker or a semantic statement comparison.

The recorded bundled native `leanchecker --silent --from-export` run returned
zero on that exact export. Its retained stdout/stderr and exporter stderr are
empty and agree with the actual local files. The recorded leanchecker and
leanexport executable hashes match the installed toolchain binaries. The
integrator executed that replay; this reviewer inspected its receipt and
artifacts. Native replay is additional evidence recorded here, without
rewriting the older core's point-in-time replay status.

The validation record distinguishes the successful fresh build from the
earlier interrupted wrong-directory cache-setup attempt, and eight recorded
legacy-module compatibility warnings from errors. It does not treat the
2,463-job summary as 2,463 fresh dependency builds. Dependency caches remain
declared inputs. The large export is retained locally outside the Git diff;
Open Math must generate and retain its own export from the immutable PR head.

## Preservation and final binding

All 65 core files are byte-identical to commit
`43664fd17014018461d6dfd64cf052c1e4afe298`; I compared them directly with Git.
The core manifest, proof sources, prior reviews and arithmetic claim boundary
are unchanged. I read the final support README, handover, validation and replay
records, and verified all 18 support-manifest entries against current bytes.
The manifest SHA-256 is
`49a5afcbea147f4b9dce441a475116831a414ee8066033dd5f4537be4f86b7ec`.
This report and its binding are excluded from that manifest to avoid a hash
cycle; the binding records their inputs and Git can bind the whole submission.

Full paranoid checking, the five additional bundled checkers and Open Math's
independent statement/application review remain pending. No frozen-39 result
is transferred to this selection. Neither the support, native replay nor a
fork merge establishes actual arithmetic cup/trace realization, all comparison
inverses, stored-functional identity, determinant normalization, limiting
descent or the main Diophantine theorem. No further support defect was found
in the bound payload.
