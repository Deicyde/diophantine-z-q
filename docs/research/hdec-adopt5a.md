# hdec-adopt5a: c9-rhof, e1-sub, x1-belyi, hodge-lattice and h5-neron in the built project

Status: task hdec-adopt5a, 2026-11-13. Results log: `scratch/hdec-adopt5a/log.md`. Generator:
`scratch/hdec-adopt5a/adopt5a.py` (uses `scratch/hdec-adopt/wrap.py`). Statement check:
`same.py`. Axiom section: `axsec.py`. Axiom output for the new entries: `axioms.txt`.

## Result

VERIFIED (01:35 PST, after the last Lean change):

- `lake build ZInQKernel` exits 0 (9996 jobs).
- `lake env lean scripts/print_axioms.lean` exits 0 and prints 464 axiom lists. Each is exactly
  `[propext, Classical.choice, Quot.sound]`, and there is no other output. 65 of them are new
  here (399 before).

All five developments named by the task are adopted, and nothing was dropped. They form five new
modules (about 3,900 lines) under `ZInQKernel/HDecomp/`, all imported from
`ZInQKernel/HDecomp.lean`:

| Module | Draft | Lines | Main theorems |
|---|---|---|---|
| `ModCurves/C9.lean` | `scratch/c9-rhof/C9.lean` | 637 | `C9Rhof.rhoF_semisimple`, `rhoF_continuous`, `c9`, `c9_R14`, `c9_r5`, `c10_via_c9` |
| `ModCurves/E1Sub.lean` | `scratch/e1-sub/E1Sub.lean` | 876 | `E1Sub.vSurjOfSurjective`, `homVK_surjective`, `rhoF_subrep_J`, `rhoF_subrep_JL`, `E1_R16`, `g13_constituent'` |
| `ModCurves/X1Belyi.lean` | `scratch/x1-belyi/X1Belyi.lean` | 377 | `X1Belyi.belyiX1_of_leaves`, `x1ModelExists_of_leaves`, `modCurveLeaves_of` |
| `Faltings/HodgeLattice.lean` | `scratch/hodge-lattice/HodgeLattice.lean` | 1181 | `ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_tangent`, `omegaLocal`, `genericFibreStalkIso` |
| `Faltings/H5Neron.lean` | `scratch/h5-neron/H5Neron.lean` (see below) | 855 | `ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all`, `stableFaltingsHeight_add_le'`, `productGroupModelExists` |

In terms of the decomposition, these glue targets are now Lean theorems in the build:

- `LeafModCurves.VSurjOfSurjective`, proved from Faltings and I3.M0 (`E1Sub.vSurjOfSurjective`);
- `X1ModelExists` and `BelyiX1`, proved from five leaves (`X1Belyi`);
- C9, the identification of R16's `ρ_{f,ι}` against R14 and against C8's `r₅` (`C9Rhof`);
- `HodgeLatticeTheorem`, proved from `TangentDimAtOrigin` and `DimBaseChange`;
- H5 in the form R19-R21 need, proved from the leaves N1 and N2 and glue (`H5Neron`).

**Statements are unchanged** (VERIFIED, `same.py`: ALL SAME). After deleting the `import` and
`#print` lines and the one-paragraph adoption docstring, each module has the same text as its
draft, up to whitespace. Each module also has exactly the draft's imports. The only edits are
moving `#print axioms` lines to `scripts/print_axioms.lean`, collapsing runs of blank lines, and
wrapping lines. All 17 lines over 100 characters were wrapped by hand: 14 code lines (whitespace
only) and 3 comment lines. `wrap.py` runs afterwards but finds nothing left to wrap.

Leaves stay `def … : Prop`. grep finds `sorry` and `axiom` only inside comments ("no `sorry`, no
`axiom`"). No line of a changed Lean file is longer than 100 characters (both VERIFIED). No build
log was saved.

## Verbatim copies

`scratch/hdec-adopt3/dups.py` was run on the five drafts. **No draft declaration is a verbatim
copy of an HDecomp declaration**, so no import replaced any code. The scan found 11 declarations
that share a last name component with HDecomp code (for example `E1Sub.bcPt` and
`LeafQM.AV.bcPt`, or `X1Belyi.TorsionStructure` and `PkgI2.TorsionStructure`). All have different
code and live in other namespaces. No full name is declared in two drafts.

C9 carries its own copies of five leaves from `scratch/h-decomposition/Leaves.lean`, which is not
in the build:
- `C9Rhof.FrobeniusDense` (T18);
- `PkgI4.EigenformRepExists`, `PkgI4.EigenformTwist` and `PkgI4.NewformOfEigenform` (R14, T24,
  T25);
- `PkgI4.GaloisRep.AttachedUpToTwist`.

They are kept as they are. **Merge risk:** if a later adoption brings `h-decomposition/Leaves.lean`
or `pkg-I4` into the build, the four `PkgI4.*` names will clash. That adoption should then import
`ModCurves.C9` or delete these copies.

## h5-neron: source and what was not adopted

- **h5-neron is not in this task's base.** `wip/integrate-w35c` does not contain it: the merge
  base of `origin/wip/h5-neron` (b7c1dc21) with this branch is 01267822. The draft was read with
  `git show origin/wip/h5-neron:scratch/h5-neron/H5Neron.lean` and saved as
  `scratch/hdec-adopt5a/src/H5Neron.lean`. The branch was not merged, so this task changes no file
  outside its own paths. The module docstring names the source commit. When `wip/h5-neron` is
  merged at integration, `docs/research/h5-neron.md` and `scratch/h5-neron/` arrive with it, with
  no conflict.
- **Adopted:** `H5Neron.lean`, the combined file of parts A-E. Its 27 `#print axioms` targets are
  all in the axiom script.
- **Not adopted:** `scratch/h5-neron/BaseChange.lean` (part F). It is partial: its main theorem
  `groupModelBaseChangeExists` (glue H4b) fails with a kernel deterministic timeout, and the proof
  is kept only as a comment. Only its helper lemmas compile. The separate files `Neron.lean`,
  `ZeroAV.lean`, `Reduction.lean` and `ProductModel.lean` are covered by the combined file.

## Docstring repairs (asked for by the task)

All three are docstring-only (VERIFIED by `git diff`, and the build passes):

1. **`LeafModCurves.VSurjOfSurjective`** (`ModCurves/Glue.lean`). The old text said "by Poincaré
   reducibility, T8 … isogenies are isomorphisms on `V_ℓ`". It now says the target is proved as
   `E1Sub.vSurjOfSurjective` from `FaltingsSemisimple`, `FaltingsTate` and `TateModuleFree`,
   without Poincaré reducibility or isogeny theory (e1-sub §1). It sketches the argument: a stable
   complement of the image, Faltings' Tate theorem, and injectivity of `π^*` because `π` is
   dominant and `A` separated. The `def` itself is unchanged.
2. **`LeafModCurves.Ej`** (`ModCurves/Defs.lean`). The old text gave the older model
   `y² + xy = x³ − 36/(j−1728)x − 1/(j−1728)`. It now gives Mathlib v4.35's `ofJNe0Or1728`:
   `y² + (j−1728)xy = x³ − 36(j−1728)³x − (j−1728)⁵`, with `Δ = j²(j−1728)⁹`. The model was
   VERIFIED in `Mathlib/AlgebraicGeometry/EllipticCurve/ModelsWithJ.lean`, and `Δ` is taken from
   x1-belyi's finding 1.
3. **`R03_LinYang`** (`LeafPush2/R3.lean`). "existence of the polarization: SPECULATIVE in the
   repository, under review in rv-qm-polar" now reads: Lemma P (rv-qm-polar §0); for a fixed `μ`,
   the type-`μ` principal polarization exists and is unique in characteristic 0; VERIFIED as an
   argument, with lattice cores compiled in `QM/Polar.lean`; published locators UNVERIFIED. This is
   the same wording hdec-adopt4 used in `QM/`. The Baba–Granath citation is kept.

## Edits to shared files (for the merge with the parallel adoption task)

- `ZInQKernel/HDecomp.lean`: one block of five `import` lines, appended **after the last existing
  import line**. Lean does not allow imports after the closing docstring, so the block cannot go
  at the very end of the file. The docstring, which lists the adopting tasks, was left unchanged to
  keep the merge simple. Adding "hdec-adopt5a" there is a one-word follow-up.
- `scripts/print_axioms.lean`: one block at the end of the file, a two-line comment and 65
  `#print axioms` lines. These are the drafts' 62 targets plus `E1Sub.rhoF_semisimple_of_surj`,
  `X1Belyi.modCurveLeaves_of` and `ZInQ.DefFaltings.HodgeLattice.tangentDimAtOrigin_of`.

## What remains (not done here)

- The leaves and glue Props these modules introduce stay hypotheses:
  - x1-belyi: T1, T2, M1, M2, M3;
  - hodge-lattice: `TangentDimAtOrigin` (or `RegularAtOrigin` with `DimAtOrigin`) and
    `DimBaseChange`;
  - h5-neron: the leaves N1 and N2, and the glue `ModelHeightBaseChange`,
    `GroupModelBaseChangeExists`, `OpenSubgroupHeight` and `ProductModelHeight`;
  - C9: T18, T19, R14, T24 and T25.

  hodge-lattice's `DimBaseChange` is likely the same statement as the `DimBaseChange` glue of
  `scratch/g0-split/Split.lean`. Neither that file nor `scratch/h-decomposition/Leaves.lean` is in
  this base, so this was not checked (UNVERIFIED).
- `scratch/h-decomposition/Leaves.lean` and `docs/research/h-decomposition.md` (outside this
  task's files) still list `VSurjOfSurjective`, `X1ModelExists`/`BelyiX1`, C9 and
  `HodgeLatticeTheorem` as open glue. Their Lean proofs are now in the build under the names above.
- h5-neron's H4b (`BaseChange.lean`) is still unproved because of the kernel timeout.

## How to reproduce

1. Make `scratch/hdec-adopt5a/src/H5Neron.lean` available: it is committed here, and is
   `git show b7c1dc21:scratch/h5-neron/H5Neron.lean`.
2. Run `python3 -I scratch/hdec-adopt5a/adopt5a.py`. It regenerates the five modules from the
   drafts, byte-identical (VERIFIED).
3. Run `python3 -I scratch/hdec-adopt5a/same.py`. It should print `ALL SAME`.
4. `axsec.py` appends the axiom section once; it refuses to run if the section is already present.
5. Run `lake build ZInQKernel`, then `lake env lean scripts/print_axioms.lean`.
