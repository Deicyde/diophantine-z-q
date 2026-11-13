# leaf-fold: the closed leaves folded into the H decomposition; what remains open

Status: research note (task leaf-fold, 2026-11-13). Base 89a5e60e (origin/wip/integrate-w38).
Edited: `scratch/h-decomposition/Leaves.lean`, `docs/research/h-decomposition.md`. New:
`scratch/leaf-fold/` (scripts, parts, compile logs, `log.md`). No file under `ZInQKernel/`,
`blueprint/` or another task's directory was edited.

Marks: **VERIFIED** (compiled or read here), **STANDARD** (published, with a reference),
**UNVERIFIED** (a locator recalled, not checked).

## 0. Main result

```lean
theorem HDec.HSyn.sixContactMin_of_open (r : OpenResearchLeaves) (t : OpenTextbookLeaves)
    (gp : GluePieces) : ZInQ.SixContactMin
```

Its hypotheses are exactly the leaves still open and the ten glue pieces (unchanged).
`#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

__COMPILE__

**Open leaves (the list for the announcement): 50 = 23 research-level + 27 textbook.**

- Research-level, all 23 (26 fields of `OpenResearchLeaves`; none is proved): R1(a,c,d) with R2 and
  R5 on `X₆` (`r1r2`), R1(b) (`r1an`, opaque), R1(d) reciprocity (`r1rec`), R3, R4, R5(ii), R5(i),
  R6, R7(a), R7(b), R8, R9(a), R9(b), **R10 corrected**, R11+R12, R13, **R14 corrected**, R15, R16,
  R17 (opaque), R18, R19, R20, R21, R22, H5.
- Textbook, 27 of 35 (26 fields of `OpenTextbookLeaves`): T1, T3, T4, T5, T6, T7, T8, T9, T10,
  T11(a), T11(b), T14(a′), T14(b′), T16(b), T23, T24, T26, T27, T28, T29(a), T29(b), T33, T34, T35,
  T36-T40 (`x1`), T41.

**Closed and folded in (no longer hypotheses):** T2, T15, T16(a), T17, T18, T20, T21 (global
forms), T25, T31; with T13, T19, T22, T30, which leaf-adopt3 had already removed (T30 now has a
closed proof too).

## 1. How the closed proofs enter `Leaves.lean`

**The obstacle (VERIFIED by grep and by the first compile).** Every Contrib proof is stated over
the kernel port `ZInQKernel/HDecomp/`, which declares this file's names at the root (for example
`PkgI6.LocalH2CardC` is in both `ZInQKernel/HDecomp/Conductor/I6Base.lean` and `Leaves.lean`).
Importing a Contrib module into the file as it was gives "already declared" errors.

**The fix.** The whole body of `Leaves.lean` is wrapped in `namespace HDec … end HDec`. Lean
resolves an identifier innermost namespace first, so inside `HDec` every reference still means
the file's own copy, while the imported kernel copy keeps its root name. The edit is mechanical
(`scratch/leaf-fold/wrap.py`); `scratch/leaf-fold/assemble.py` rebuilds the file from the base
(`git show 89a5e60e:scratch/h-decomposition/Leaves.lean`) and the two new parts
`scratch/leaf-fold/parts/t2.lean`, `parts/tail.lean`. Besides the wrapper, the edits are:

1. imports: `ZInQKernel.Contrib.{BrauerT14T15.Main, LocalKW.T30, KroneckerWeber.Leaves,
   Chebotarev.FrobeniusDense, Different.Global, T25.NewformOfEigenform, T31.Main}` and
   `ZInQKernel.HDecomp.Textbook.BrauerNesbitt`;
2. the five declarations named `_root_.X` become `_root_.HDec.X`, and the dot-notation uses of the
   renamed `PeriodPair.lattice1` become explicit;
3. `open ZInQ` after `HDec.ZInQ` exists opens both halves (`open _root_.ZInQ ZInQ …`);
4. Tau Ceti declares a root `IsArithFrobAt.eq_of_isUnramifiedAt` (group-action form, needs
   `FaithfulSMul`). It captured the dot notation `hσ.eq_of_isUnramifiedAt` in
   `GlueC10.restrictNormal_eq_of_frob`, meant for Mathlib's
   `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`; that lemma is now called explicitly;
5. heartbeat limits inside `HDec`: `maxHeartbeats 1000000`, `synthInstance.maxHeartbeats 200000`.
   With the Tau Ceti instances in scope, 17 instance searches (e.g. `Module.IsTorsionFree ℚ_[p]
   ℂ_[p]`, `IsMulTorsionFree Gal(L/ℚ_p)`) and `LeafQM.AV.QML3.Iso.twist` exceeded the defaults;
6. T19's proof `TSkolemKW.brauerNesbittChar0`: its step `simp [LinearEquiv.conj_apply]; rfl` fails
   with the larger simp set. The same proof compiles in the kernel module
   `ZInQKernel.HDecomp.Textbook.BrauerNesbitt`, so the file's theorem is now that one
   (`_root_.TSkolemKW.brauerNesbittChar0`), converted by unfolding.

Names: every declaration of the file is now `HDec.…` (e.g. `HDec.HSyn.sixContactMin_of_leaves`).
Inside the file and in this note the prefix is omitted.

## 2. The closed leaves: each Contrib Prop against the bundle's field

Each field is a theorem `HSyn.tN_proved` whose proof is the Contrib theorem, so Lean checks that
the two Props are definitionally equal (VERIFIED: compiled). In addition `#hdec_same HDec.X` (a
command defined in the file) compares `HDec.X` with the root `X` syntactically: the types and, for
definitions, the bodies, after deleting the prefix `HDec.`, recursively through every `HDec.`
constant they mention (for theorems, the types only).

__TABLE__

## 3. Statement repairs

- **R14 → `G0Galois.R14Det`** (g0-mod-galois §3). R14 with its published determinant clause
  `det ρ_g = ε·χ_ℓ^{k−1}`, `ε` of finite image (Shimura 1971 Thm 7.14, Deligne 1971, Deligne–Serre
  1974; UNVERIFIED locators), which G12's determinant argument needs. Copied verbatim from
  `scratch/g0-mod-galois/part_det.lean` with `toRingEquivQ`, `cycQ`. It is the field `r14` of
  `OpenResearchLeaves`; `HSyn.eigenformRepExists_of_r14Det` gives the old field.
- **R10 → `PkgI4.DeRhamComparisonHT`** (g9-derham, finding F1). The old field gives the
  Hodge–Tate multiplicities `g` at `0` and `−1` but not `0` at every other weight, which G9's
  output `HasHTWeights p ρ {0, −1}` needs. The corrected statement adds that clause
  (`PkgI4.R10Weights`, verbatim g9-derham's `G9Bridge.R10Weights`), part of the published
  Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g` (Tate 1967, Faltings 1988;
  UNVERIFIED locators). `PkgI4.deRhamComparisonHT_iff : DeRhamComparisonHT ↔ DeRhamComparison ∧
  R10Weights`. It is the field `r10` of `OpenResearchLeaves`.
- **G10 → `G0Galois.G10GlueConcrete`** (g10-odd). g0-mod-galois's glue Prop `G10Glue` assumed the
  inert placeholders `HSyn.T11_RiemannGAGA`, `HSyn.T12_ArtinComparison`; the corrected statement
  assumes the concrete leaves T11(a), T11(b), T35, T5, T26, R9(b). Its core `ConjTwistNontrivial`
  (glue) is recorded too. Both are definitions in the file (`resQ`, `Vb`, `tate`, `Intertwines`,
  `G10Out` copied verbatim). G10 lives inside the glue piece `GluePieces.modularConstituent`, so
  neither is a hypothesis of `sixContactMin_of_open`; g10-odd's reductions (`ConjTwistNontrivial →
  G10Glue`, `ConjTwistFromLeaves → G10GlueConcrete`) are in `scratch/g10-odd/` and are not copied.

## 4. What remains

1. The 50 open leaves of §0.
2. The ten glue pieces of `GluePieces` (h-decomposition §3), unchanged.
3. T14(a′), T14(b′) could be replaced by the single textbook statement `KummerIndexBound` (the
   Kummer case of the second inequality, over Tau Ceti's idele class groups;
   `HSyn.t14_of_kummerIndexBound`, compiled). Not done: the bundle keeps the published T14 forms.
4. The `HDec` wrapper should disappear when the file is unified with the kernel port (WP1): the
   duplicated definitions would then be the kernel's, and the conversions in §2 would be
   identities.

## 5. Files

- `scratch/leaf-fold/wrap.py`, `assemble.py` (rebuild `Leaves.lean`), `parts/t2.lean`,
  `parts/tail.lean`, `closure.py` (kernel modules imported), `doc_edit.py`, `doc_table.py`,
  `doc_par0.md`, `doc_remaining.md` (edits of the note), `compile*.txt`, `log.md`.
