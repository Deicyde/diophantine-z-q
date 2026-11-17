# Work in progress: native closure toward `neronOggShafarevichSep`

Status: **work in progress, not a proof.** `neronOggShafarevichSep` (main, `docs/one-proof/OPEN.md`) remains an
open leaf. Nothing on this branch claims to discharge it yet.

Base: `main` at `c0f3d085c430e97e6e2cbc8d66d4a3f064f47b9f` (the deliverable's import closure of main modules is byte-identical at current main).
Toolchain: the repository's pinned Lean 4.35.0 / Mathlib.

## What this branch contains

610 new source files, added on top of `main` without modifying any existing file:

* the converse route toward `NOSProof.NOSConverseSep` and the glue that proves main's
  `NOSSepDict.NeronOggShafarevichSep` from it (`ZInQKernel/Contrib/CloudR2NOS/NOSSepGlue/`); the forward
  directions come from the owner's `wip/nos-proof` branch (`NeronOggShafarevich.lean`, commit `e9828e92`,
  included byte-for-byte and credited);
* the native theorem-of-the-square cone it consumes (`ZInQKernel/Contrib/CloudR2Poincare/`);
* regenerated support modules adapted from FLT and Mathlib sources (Apache-2.0; attribution in each file header);
* earlier native properness supplier copies (`ZInQKernel/Contrib/CloudW01Spread/...`) still imported by this closure.

`MainLeafConditional` proves the open leaf **assuming** the converse statement; `MainLeaf` (unconditional) is
still blocked by the open items below.

## Milestone (2026-11-17): final shape checked against main's real definitions

`ZInQ.Contrib.CloudR2NOS.NOSSepGlue.neronOggShafarevichSep_of_converse` compiles at Lean's default limits, on top of
main's own compiled modules and the owner's `NeronOggShafarevich.lean`. Its conclusion is main's
`NOSSepDict.NeronOggShafarevichSep` exactly, and `#print axioms` reports only `propext`, `Classical.choice` and
`Quot.sound`. It takes as a **hypothesis** the converse over the algebraic closure:

```
∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  (w : ValuationSubring (AlgebraicClosure K)), w.comap (algebraMap K (AlgebraicClosure K)) = O →
  ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
    {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite → HasGoodReduction A O
```

So the open leaf reduces, by compiled proof, to this converse statement. **The converse itself is not yet proved**;
it is what the rest of this branch is building toward (`MainLeaf`, unconditional, is still blocked).

## Native build status (Lean default proof limits; no raised numeric options)

* 424 of the 608 new modules on this branch have compiled so far in our native build, on top of main's own
  compiled modules; the rest are queued or blocked.
* Open blockers on the path to `MainLeaf`:
  * the special-fibre torsion results (two FLT-derived solution modules; the supporting FLT port is being
    re-proved at default limits and is not on this branch yet);
  * strict-henselization helper modules (Raynaud family, requested from another lane);
  * two `Review.ModuleLine*` modules being re-authored;
  * three remaining modules of the theorem-of-the-square cone and one closed-section presentation module.

## Provenance notes

* Comment-only normalization: internal tooling and work-session reference tokens were removed from comment
  headers in later commits on this branch (no code change). Two superseded helper-authored files were removed;
  the original modules they stood in for will be added once recovered.
* Files compile individually with Lean's default limits; any non-numeric local switch carried over from an
  upstream source is disclosed in that file's header.

This branch is updated as native builds land. It is not a pull request.
