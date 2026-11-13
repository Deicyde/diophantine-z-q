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

VERIFIED (final run, 2026-11-13 06:54 PST): `lake env lean scratch/leaf-fold/Full.lean` (the file
installed as `scratch/h-decomposition/Leaves.lean`, 35 850 lines) exits 0 in 8 min 57 s, with
0 errors and no `declaration uses 'sorry'`. All 210 `#print axioms` outputs are
`[propext, Classical.choice, Quot.sound]` (counted by script), including
`HDec.HSyn.sixContactMin_of_open`, `HDec.HSyn.sixContactMin_of_leaves`, each `HSyn.tN_proved`
and `HDec.TBrauerPurity.abhyankarDVR`. There are 2 `opaque` (R1(b), R17) and no `axiom`. Output:
`scratch/leaf-fold/compile4.txt`. Before compiling, build the imported modules:
`lake build ZInQKernel.Contrib.BrauerT14T15.Main ZInQKernel.Contrib.LocalKW.T30
ZInQKernel.Contrib.KroneckerWeber.Leaves ZInQKernel.Contrib.Chebotarev.FrobeniusDense
ZInQKernel.Contrib.Different.Global ZInQKernel.Contrib.T25.NewformOfEigenform
ZInQKernel.Contrib.T31.Main ZInQKernel.HDecomp.Textbook.BrauerNesbitt` (about 9 min from a
Mathlib-only build).

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
5. inside `HDec`: `attribute [-instance]` on Tau Ceti's `FinitePadicExtension.toAlgebra`,
   `.ofInstances`, `.toModuleFinite`, `.toValuativeExtension`, and `maxHeartbeats 1000000`. With
   those instances in scope every `Algebra ℚ_[p] K` subgoal searches `FinitePadicExtension K p`;
   in the first compile 17 instance searches (e.g. `Module.IsTorsionFree ℚ_[p] ℂ_[p]`,
   `IsMulTorsionFree Gal(L/ℚ_p)`, `Normal ℚ_[p] K`) and `LeafQM.AV.QML3.Iso.twist` timed out.
   Raising `synthInstance.maxHeartbeats` instead made each failing search take minutes. With the
   four instances off, `Module.IsTorsionFree ℚ_[p] ℂ_[p]` takes 0.6 s (probes
   `scratch/leaf-fold/probe/P1.lean`, `P2.lean`). The file's own proofs never use them. (A local
   `synthInstance.maxHeartbeats 200000` added on `htSpace_cycRep_eq_bot` before the culprit was
   found is still there; it is harmless.)
6. T19's proof `TSkolemKW.brauerNesbittChar0`: its step `simp [LinearEquiv.conj_apply]; rfl` failed
   in the first compile, with the Contrib modules in scope (whether the instance fix of item 5
   would also repair it was not tried). The same proof compiles in the kernel module
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

Results (VERIFIED: output of the final compile, `scratch/leaf-fold/compile4.txt`):

| Leaf | Bundle field (this file) | Closed proof (Contrib) | `exact` (defeq) | `#hdec_same` |
| --- | --- | --- | --- | --- |
| T2 | `t2 : PkgI2.AbhyankarDVR.{0}` | t-brauer-purity's proof, copied in (`HDec.TBrauerPurity.abhyankarDVR`; T2Full's copy of the definition is textually this file's) | yes | `PkgI2.AbhyankarDVR` (kernel copy in `HDecomp/Objects.lean`): verbatim |
| T15 | `t15 : PkgI6.LocalH2CardC` | `ZInQ.Contrib.BrauerT14T15.localH2CardC` | yes | verbatim (4 constants) |
| T16(a) | `t16a : ∀ p [Fact p.Prime], PkgI6.LocalKroneckerWeber p` | `ZInQ.Contrib.localKroneckerWeber` | yes | verbatim |
| T17 | `t17 : TSkolemKW.KW.KroneckerWeberCyclic` | `ZInQ.Contrib.KroneckerWeber.kroneckerWeberCyclic` | yes | verbatim |
| T17 (old form) | `HSyn.KroneckerWeber` (not a field since leaf-adopt3) | `ZInQ.Contrib.KroneckerWeber.hSynKroneckerWeber` | yes | verbatim against `HSynKroneckerWeber` (`#hdec_same_as`) |
| T18 | `t18 : PkgI6.ChebotarevExists` | `ZInQ.Contrib.chebotarevExists` | yes | verbatim |
| T18 (density form) | `HSyn.FrobeniusDense` (proved from `t18` before) | `ZInQ.Contrib.frobeniusDense` | yes | verbatim against `ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense` and its copies of `HSyn`'s definitions (5 constants) |
| T20 | `t20 : GlueConductor.HilbertDifferentFormula` | `ZInQ.Contrib.Different.hilbertDifferentFormula` | yes | verbatim (3 constants) |
| T21 | `t21 : GlueConductor.SerreDifferentBound` | `ZInQ.Contrib.Different.serreDifferentBound` | yes | verbatim |
| T25 | `t25 : PkgI4.NewformOfEigenform` | `T25.newformOfEigenform_leaf` | yes | **one difference**: the elaborated body of `PkgI4.HasNebentypus` (see below); the other 7 constants verbatim |
| T30 | (removed by leaf-adopt3; `GlueDescent.B2Q.LeafSqrtCrit`) | `ZInQ.Contrib.leafSqrtCrit` | yes | verbatim (7 constants) |
| T31 | `t31 : GlueDescent.B2Q.LeafUnramified` | `ZInQ.Contrib.T31.leafUnramified` | yes | verbatim (11 constants) |
| T14(a′), T14(b′) (not closed) | `t14a`, `t14b` | `…brauerHasse2C_of_kummerIndexBound`, `…brauerReciprocity2C_of_kummerIndexBound` (from `KummerIndexBound`) | yes | verbatim |

"Verbatim" means: equal after deleting `HDec.` and replacing every proof constant (a theorem, an
auxiliary `_proof_n`, a `Fact` instance) by "a proof of" its normalized type. Proof constants
get different automatic names in the two files (for example `instFactPrimeValNat_scratch` against
the kernel's own name for `local instance : Fact p.Prime`), and proof irrelevance makes them
interchangeable. The first version of the checker, without this normalization, reported
exactly those name differences and nothing else for T16(a), T17, T30 and T31.

**The one difference (T25).** `PkgI4.HasNebentypus` has the same source text in both files
(`Leaves.lean` §2 of `PkgI4` and `ZInQKernel/HDecomp/Conductor/LadicCond.lean`), with the same
`open scoped MatrixGroups ModularForm`. A standalone copy elaborated with the same imports
matches the kernel's (probe `scratch/leaf-fold/probe/P4.lean`). So the elaborated terms differ
only in this file's context, presumably an instance path (an instance this file declares earlier
inside `HDec`, which the kernel module does not import). The two Props are **definitionally
equal**: `HSyn.t25_proved` is accepted by `exact`. Not investigated further.

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
