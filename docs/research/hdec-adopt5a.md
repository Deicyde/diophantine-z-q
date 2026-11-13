# hdec-adopt5a: c9-rhof, e1-sub, x1-belyi, hodge-lattice and h5-neron in the built project
# (and glue H4b proved)

Status: task hdec-adopt5a, 2026-11-13. Results log: `scratch/hdec-adopt5a/log.md`. Generators:
`scratch/hdec-adopt5a/adopt5a.py` (uses `scratch/hdec-adopt/wrap.py`) and `h4b.py`. Statement
check: `same.py`. Axiom section: `axsec.py`. Axiom output for the new entries: `axioms.txt`.

## Result

VERIFIED (02:01 PST, after the last Lean change):

- `lake build ZInQKernel` exits 0 (9997 jobs).
- `lake env lean scripts/print_axioms.lean` exits 0 and prints 471 axiom lists. Each is exactly
  `[propext, Classical.choice, Quot.sound]`, and there is no other output. 72 of them are new
  here (399 before).

All five developments named by the task are adopted, and nothing was dropped. They form five
modules (about 3,900 lines) under `ZInQKernel/HDecomp/`. A sixth module is new work: it adopts
h5-neron's unfinished part F and **completes it, proving glue H4b** (`GroupModelBaseChangeExists`,
§H4b below). All six are imported from `ZInQKernel/HDecomp.lean`:

| Module | Draft | Lines | Main theorems |
|---|---|---|---|
| `ModCurves/C9.lean` | `scratch/c9-rhof/C9.lean` | 637 | `C9Rhof.rhoF_semisimple`, `rhoF_continuous`, `c9`, `c9_R14`, `c9_r5`, `c10_via_c9` |
| `ModCurves/E1Sub.lean` | `scratch/e1-sub/E1Sub.lean` | 876 | `E1Sub.vSurjOfSurjective`, `homVK_surjective`, `rhoF_subrep_J`, `rhoF_subrep_JL`, `E1_R16`, `g13_constituent'` |
| `ModCurves/X1Belyi.lean` | `scratch/x1-belyi/X1Belyi.lean` | 377 | `X1Belyi.belyiX1_of_leaves`, `x1ModelExists_of_leaves`, `modCurveLeaves_of` |
| `Faltings/HodgeLattice.lean` | `scratch/hodge-lattice/HodgeLattice.lean` | 1181 | `ZInQ.DefFaltings.HodgeLattice.hodgeLatticeTheorem_of_tangent`, `omegaLocal`, `genericFibreStalkIso` |
| `Faltings/H5Neron.lean` | `scratch/h5-neron/H5Neron.lean` (see below) | 855 | `ZInQ.H5Neron.stableFaltingsHeight_eq_neron_all`, `stableFaltingsHeight_add_le'`, `productGroupModelExists` |
| `Faltings/H5BaseChange.lean` | `scratch/h5-neron/BaseChange.lean` (compiled part) + new assembly | 216 | `ZInQ.H5Neron.groupModelBaseChangeExists` (**new**), `bcGen'_isMonHom` |

In terms of the decomposition, these glue targets are now Lean theorems in the build:

- `LeafModCurves.VSurjOfSurjective`, proved from Faltings and I3.M0 (`E1Sub.vSurjOfSurjective`);
- `X1ModelExists` and `BelyiX1`, proved from five leaves (`X1Belyi`);
- C9, the identification of R16's `ρ_{f,ι}` against R14 and against C8's `r₅` (`C9Rhof`);
- `HodgeLatticeTheorem`, proved from `TangentDimAtOrigin` and `DimBaseChange`;
- H5 in the form R19-R21 need, proved from the leaves N1 and N2 and glue (`H5Neron`);
- **h5-neron's glue H4b `GroupModelBaseChangeExists`, proved here** (`H5BaseChange`): a group model
  of `A_L` over `𝓞_L` base-changes to a group model of `A_{L'}` over `𝓞_{L'}`. So
  `stableFaltingsHeight_eq_neron_all` now needs three glue statements instead of four.

**Statements are unchanged** (VERIFIED, `same.py`: ALL SAME, for the five adopted drafts). After deleting the `import` and
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
- **Part F** (`scratch/h5-neron/BaseChange.lean`, partial in the draft) is adopted as
  `Faltings/H5BaseChange.lean`, and its main theorem is now proved (§H4b).
- The separate files `Neron.lean`, `ZeroAV.lean`, `Reduction.lean`, `ProductModel.lean` and
  `T.lean` are not adopted. The combined file covers them.

## H4b: `groupModelBaseChangeExists` (new proof, VERIFIED)

The draft's assembly of `bcGen_isMonHom` passed the elaborator, but the kernel reported a
deterministic timeout. The draft's diagnosis was "a mismatch in hidden instance arguments". The
experiments here (`scratch/hdec-adopt5a/Exp1.lean`-`Exp3.lean`, outside the build) locate it
elsewhere: the timeout is in the equation `(bcGen 𝒢).hom = composite`. The draft closes it by
`rfl`. `rw` or `simp` followed by a final definitional step also time out.

The cause is the types. `bcGen`'s declared source and target are `genericFibre L' _` and
`(A.baseChange L').X`, and `𝒢.gen`'s target is `(A.baseChange L).X`. None of these is
syntactically the object in the composite, so the kernel must unfold the category structure of
`Over`.

The fix, in the hdec-adopt5a section of the module (`H4bAssembly.part`):
- `genIso 𝒢`: `𝒢.gen` restated at the unfolded types, with `genIso_isMonHom := 𝒢.gen_hom`.
- `bcGen' 𝒢`: the same six-step isomorphism, built at the composite's own type.
- `bcGen'_hom`: its `hom` as the six-fold composite. The proof is an explicit chain of
  `Iso.trans_hom` and `congrArg₂` steps. Each one-step lemma passes the kernel quickly, while a
  single `simp only` over the same lemmas still times out.
- `bcGen'_isMonHom`: by `rw [bcGen'_hom]; infer_instance`, from the draft's compiled lemmas
  `isMonHom_pbCompHom`, `isMonHom_pbCompInv` and `isMonHom_pbEq`. The instance terms gave no
  trouble.
- `groupModelBaseChangeExists`: as in the draft, with `bcGen'` used directly as the new
  `GroupModel`'s `gen`. Its type unfolds definitionally to `genericFibre L' _ ≅ (A.baseChange L').X`.

The draft's own copies of `IsBaseChangeOf` and `GroupModelBaseChangeExists` are verbatim in
`H5Neron.lean`; `h4b.py` asserts this. They are replaced by the import, so the theorem proves
exactly the glue Prop stated in `H5Neron`. The draft's compiled lemmas, `bcGen` included, are kept
unchanged. Only the unfinished comment block is dropped. Statement check: the module states
`theorem groupModelBaseChangeExists : GroupModelBaseChangeExists`, with no hypotheses.

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

- `ZInQKernel/HDecomp.lean`: one block of six `import` lines, appended **after the last existing
  import line**. Lean does not allow imports after the closing docstring, so the block cannot go
  at the very end of the file. The docstring, which lists the adopting tasks, was left unchanged to
  keep the merge simple. Adding "hdec-adopt5a" there is a one-word follow-up.
- `scripts/print_axioms.lean`: one block at the end of the file, with comments and 72
  `#print axioms` lines. These are:
  - the drafts' 62 targets;
  - `E1Sub.rhoF_semisimple_of_surj`, `X1Belyi.modCurveLeaves_of` and
    `ZInQ.DefFaltings.HodgeLattice.tangentDimAtOrigin_of`;
  - for part F: the draft's 5 targets, plus `bcGen'_hom`, `bcGen'_isMonHom` and
    `groupModelBaseChangeExists`.

## What remains (not done here)

- The leaves and glue Props these modules introduce stay hypotheses:
  - x1-belyi: T1, T2, M1, M2, M3;
  - hodge-lattice: `TangentDimAtOrigin` (or `RegularAtOrigin` with `DimAtOrigin`) and
    `DimBaseChange`;
  - h5-neron: the leaves N1 and N2, and the glue `ModelHeightBaseChange`, `OpenSubgroupHeight`
    and `ProductModelHeight` (`GroupModelBaseChangeExists` is now proved);
  - C9: T18, T19, R14, T24 and T25.

  hodge-lattice's `DimBaseChange` and the `DimBaseChange` glue of g0-split say the same thing:
  `(A.baseChange L).dim = A.dim`. The g0-split version is in `scratch/g0-split/Split.lean`, which
  is not in this base; it was read at cc52155b. The two differ only in binder order and in the
  `AbVar` they use: g0-split's file is self-contained, with its own copy of `AbVar`. This was
  checked by reading only, not in Lean.
- `scratch/h-decomposition/Leaves.lean` and `docs/research/h-decomposition.md` (outside this
  task's files) still list `VSurjOfSurjective`, `X1ModelExists`/`BelyiX1`, C9 and
  `HodgeLatticeTheorem` as open glue. Their Lean proofs are now in the build under the names above.
- `docs/research/h5-neron.md` (on `wip/h5-neron`) still lists H4b as partial and unproved.

## How to reproduce

1. `scratch/hdec-adopt5a/src/H5Neron.lean` and `src/BaseChange.lean` are committed here. They
   are `git show b7c1dc21:scratch/h5-neron/<file>`.
2. Run `python3 -I scratch/hdec-adopt5a/adopt5a.py`. It regenerates the five modules from the
   drafts, byte-identical (VERIFIED).
3. Run `python3 -I scratch/hdec-adopt5a/same.py`. It should print `ALL SAME`.
   Then run `python3 -I scratch/hdec-adopt5a/h4b.py`, which writes `Faltings/H5BaseChange.lean`.
4. `axsec.py` appends the axiom section (65 entries) once and refuses to run if the section is
   already present. The 7 part-F entries and their comment line were then appended by hand.
5. Run `lake build ZInQKernel`, then `lake env lean scripts/print_axioms.lean`.
