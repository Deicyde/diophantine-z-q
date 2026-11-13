# kummer-index: leaf T14 (T14a′, T14b′) proved outright

Status: research note and Lean deliverable (task kummer-index, 2026-11-13). Base: fork main 033423ee,
with origin/wip/t1415-tc (5341a1f4) merged. Results log: `scratch/kummer-index/log.md`. Only new
files; no existing file was edited, and no Tau Ceti module was vendored or changed.

Marks: **VERIFIED** = compiled or read in the source; **STANDARD** = published; **SPECULATIVE** = assessment.

## 1. Main result (VERIFIED, compiled, standard axioms)

Leaf T14 is proved in its two cochain forms, with no hypothesis:

```lean
theorem ZInQ.Contrib.T14.kummerIndexBound : ZInQ.Contrib.BrauerT14T15.KummerIndexBound
theorem ZInQ.Contrib.T14.brauerHasse2C : PkgI6.BrauerHasse2C              -- T14a′
theorem ZInQ.Contrib.T14.brauerReciprocity2C : PkgI6.BrauerReciprocity2C  -- T14b′
theorem ZInQ.Contrib.T14.leaves_T14_T15 :
    PkgI6.BrauerHasse2C ∧ PkgI6.BrauerReciprocity2C ∧ PkgI6.LocalH2CardC
theorem ZInQ.Contrib.T14.cob_of_same_finite_support'
    (ε₁ ε₂ : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (c₁ : IsCocycle2 ε₁) (c₂ : IsCocycle2 ε₂)
    (hsame : ∀ (p : ℕ) [Fact p.Prime],
      IsCoboundary2 (resC ℚ_[p] ε₁) ↔ IsCoboundary2 (resC ℚ_[p] ε₂)) :
    IsCoboundary2 (ε₁ - ε₂)
theorem ZInQ.Contrib.T14.leafHasse : GlueDescent.B2Q.LeafHasse
```

The leaf Props, as printed by `#print`:

```lean
def PkgI6.BrauerHasse2C : Prop :=
∀ (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2),
  PkgI6.IsCocycle2 ε → PkgI6.IsCoboundary2 (PkgI6.resC ℝ ε) →
    (∀ (p : ℕ) [inst : Fact (Nat.Prime p)], PkgI6.IsCoboundary2 (PkgI6.resC ℚ_[p] ε)) →
      PkgI6.IsCoboundary2 ε
def PkgI6.BrauerReciprocity2C : Prop :=
∀ (ε : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2),
  PkgI6.IsCocycle2 ε →
    {p | ¬PkgI6.IsCoboundary2 (PkgI6.resC ℚ_[↑p] ε)}.Finite ∧
      Even ({p | ¬PkgI6.IsCoboundary2 (PkgI6.resC ℚ_[↑p] ε)}.ncard +
        if PkgI6.IsCoboundary2 (PkgI6.resC ℝ ε) then 0 else 1)
def ZInQ.Contrib.BrauerT14T15.KummerIndexBound : Prop :=
∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] [IsGalois F L]
  (p : ℕ) [Fact (Nat.Prime p)] [HasEnoughRootsOfUnity F p],
  Module.finrank F L = p → (TauCeti.GlobalNumberFields.ideleClassNormMap F L).range.index ≤ p
```

`#print axioms` (`scratch/kummer-index/axioms.txt`, from `scratch/kummer-index/Axioms.lean`):

```
'ZInQ.Contrib.T14.kummerIndexBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T14.brauerHasse2C' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T14.brauerReciprocity2C' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T14.leaves_T14_T15' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T14.cob_of_same_finite_support'' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.T14.leafHasse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Together with t1415-tc's T15 (`localH2CardC`), T14 and T15 are both off the leaf list.
`GlueDescent.B2Q.LeafHasse` and `LeafLocalTwo` (t1415-tc) are now both proved, so the Brauer step
of B2 (`PkgI6.cob_of_same_finite_support`) rests on no leaf.

## 2. Files

| File | Content |
|---|---|
| `ZInQKernel/Contrib/T14/Main.lean` | `kummerIndexBound`, `brauerHasse2C`, `brauerReciprocity2C`, `leaves_T14_T15`, `cob_of_same_finite_support'` |
| `ZInQKernel/Contrib/T14/WP3.lean` | `leafHasse` |

`lake build ZInQKernel.Contrib.T14.WP3` succeeds (9919 jobs), and so does `ZInQKernel.Contrib.T14.Main`.

## 3. The bridge (step 1 of the task)

No bridge is needed. Tau Ceti nov01 (97a5b235), module
`TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index`, was backported by kw-new as
`ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/Global/Kummer/Index.lean`. At line 245 it
proves

```lean
theorem TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_le_of_finrank_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hfin : Module.finrank K L = p) :
    (GlobalNumberFields.ideleClassNormMap K L).range.index ≤ p
```

The binders are those of `KummerIndexBound` in the same order. The objects are the same: Mathlib's
`IdeleClassGroup` and Tau Ceti's `GlobalNumberFields.ideleClassNormMap`, defined in the vendored
`NumberField/Global/Ideles/Norm/Relative.lean`. So the proof is a one-line application (VERIFIED).

The proof is the one in Milne, *Class Field Theory*, VII §6 (STANDARD; section UNVERIFIED). Take
`S` containing the places above `p` and the ramified places, with classes generating the class
group. Embed `L` in `K(U_S^{1/p})` by Kummer theory. Choose auxiliary places `T` with
`E_{S,T} ⊆ N(C_L)`. Then `[C_K : E_{S,T}K^×/K^×] · p^{#T} = p^{#S+r₁+r₂}` gives
`[C_K : N(C_L)] ∣ p`.

Compatibility (VERIFIED by compiling): the oct16 closure of t1415-tc's `BrauerT14T15.Main` (through
`Global.IdeleClass.SecondInequality`, `Global.Brauer.SumFormula`) and the nov01 closure of
`Kummer.Index` (with kw-new's Backport replacement copies of `Kummer.Norm`,
`Kummer.AuxiliaryPlaces`) load in one environment without clashing declarations.

## 4. Licence

No module was vendored and no vendored file was edited, so `ThirdParty/TauCeti/NOTICE` is
unchanged. `diffcheck2.py` reports 19 MOD-UNNOTED, none from this task: they were already on main 033423ee
(list: `scratch/kummer-index/mod-unnoted-preexisting.txt`). They are tc-port and kw-new files and
should be checked by those tasks' owners.

## 5. What remains

Nothing for T14. Suggested follow-ups:
* Integration: adopt `ZInQ.Contrib.T14.brauerHasse2C`, `brauerReciprocity2C`, `leafHasse` and
  t1415-tc's `localH2CardC`, `leafLocalTwo` in the leaf bookkeeping (STATUS.md,
  `docs/research/h-decomposition.md` rows T14, T15, WP3).
* `scratch/h-decomposition/Leaves.lean` has its own copies of `BrauerHasse2C` and
  `BrauerReciprocity2C` (lines 4921, 4927). The theorems here are about the kernel's
  `PkgI6` definitions in `ZInQKernel/HDecomp/Conductor/I6Base.lean`.
