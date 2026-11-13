# kummer-index (fleet summary)

**Main result: leaf T14 (T14a′ and T14b′) is proved outright.** All theorems below compile with
axioms `[propext, Classical.choice, Quot.sound]`.

Declarations, in new files `ZInQKernel/Contrib/T14/Main.lean` and `WP3.lean`:
- `ZInQ.Contrib.T14.kummerIndexBound : ZInQ.Contrib.BrauerT14T15.KummerIndexBound`
- `ZInQ.Contrib.T14.brauerHasse2C : PkgI6.BrauerHasse2C` (T14a′)
- `ZInQ.Contrib.T14.brauerReciprocity2C : PkgI6.BrauerReciprocity2C` (T14b′)
- `ZInQ.Contrib.T14.leaves_T14_T15 : BrauerHasse2C ∧ BrauerReciprocity2C ∧ LocalH2CardC`
- `ZInQ.Contrib.T14.cob_of_same_finite_support'` (the Brauer step of B2, with no leaf hypothesis)
- `ZInQ.Contrib.T14.leafHasse : GlueDescent.B2Q.LeafHasse`

How: t1415-tc's `KummerIndexBound` has, binder for binder, the statement of Tau Ceti nov01's
`TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_le_of_finrank_prime`
(`Global/Kummer/Index.lean`, already backported by kw-new), over the same objects (Mathlib ideles,
Tau Ceti's `ideleClassNormMap`). So no bridge was needed. The oct16 BrauerT14T15 closure and the
nov01 Index closure load together.

What compiles: `lake build ZInQKernel.Contrib.T14.WP3` succeeds (it includes `T14.Main`).

What remains: nothing for T14. The leaf bookkeeping (STATUS, h-decomposition rows T14, T15, WP3)
should adopt these. No Tau Ceti module was vendored or changed, so NOTICE is unchanged. diffcheck2
shows 19 MOD-UNNOTED, all already on main and none from this task (list in
`scratch/kummer-index/mod-unnoted-preexisting.txt`).

Report: `docs/research/kummer-index.md`. Log: `scratch/kummer-index/log.md`.
