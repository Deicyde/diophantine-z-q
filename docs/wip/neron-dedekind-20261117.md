# Work in progress: Néron models over Dedekind bases (`neronSchemeExtensionDedekind`)

Status: **work in progress, not a proof.** `neronSchemeExtensionDedekind` (main, `docs/one-proof/OPEN.md`) remains
an open leaf. Nothing on this branch claims to discharge it.

Base: `main` at `c0f3d085c430e97e6e2cbc8d66d4a3f064f47b9f`. Toolchain: the repository's pinned Lean 4.35.0 / Mathlib.

## What this branch contains

445 new source files (no existing file is modified): the strict-henselization / Néron-model construction
infrastructure (`ZInQKernel/Contrib/CloudR2NeronExistence/Henselian/...`), its vendored support modules, and the
supporting source definitions shared with the `neronOggShafarevichSep` work.

## Native build status (Lean default proof limits; no raised numeric options)

* 202 of these files compile in our native build on top of main's own modules.
* One default-limit re-proof (a double-stalk ring-isomorphism lemma) is still being written; it and its 3
  dependents are not yet compiled.
* 239 further modules wait on 30 supporting source modules that are not yet
  part of this snapshot.
* The arbitrary-Dedekind adapter and the all-test atlas needed for the open leaf are still being written.

## Provenance notes

* Comment-only normalization: internal work-session reference tokens and local clone paths were replaced in
  16 comment headers (no code change).
* Files adapted from the Lean FLT project (Apache-2.0) carry attribution headers; see
  `ZInQKernel/Contrib/CloudR2NOS/NOTICE` on the companion branch `wip/nos-sep-closure-20261117`.

This branch is updated as native builds land. It is not a pull request.
