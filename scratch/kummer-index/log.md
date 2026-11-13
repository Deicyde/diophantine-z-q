# kummer-index results log

- Base: fork main 033423ee + merge origin/wip/t1415-tc (5341a1f4). kw-new (0cd896f3) already in main.
- VERIFIED (read): `KummerIndexBound` (ZInQKernel/Contrib/BrauerT14T15/GlobalT14.lean:106) and
  `TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_le_of_finrank_prime`
  (ZInQKernel/Contrib/TauCeti/NumberTheory/ClassFieldTheory/Global/Kummer/Index.lean:245, nov01 97a5b235,
  backported by kw-new) have the same statement, binder for binder (K L : Type, Field, NumberField,
  Algebra, IsGalois, p, Fact p.Prime, HasEnoughRootsOfUnity K p, finrank = p →
  (GlobalNumberFields.ideleClassNormMap K L).range.index ≤ p). Same objects: no bridge needed.
- VERIFIED (compiled): `lake build ZInQKernel.Contrib.T14.Main` and `ZInQKernel.Contrib.T14.WP3` succeed
  (9919 jobs; the oct16 BrauerT14T15 closure and the nov01 Kummer.Index closure with kw-new's Backport
  replacements load together, no duplicate declarations).
- VERIFIED: `ZInQ.Contrib.T14.kummerIndexBound : KummerIndexBound`, `brauerHasse2C : PkgI6.BrauerHasse2C`,
  `brauerReciprocity2C : PkgI6.BrauerReciprocity2C`, `leaves_T14_T15`, `cob_of_same_finite_support'`,
  `leafHasse : GlueDescent.B2Q.LeafHasse`: all `[propext, Classical.choice, Quot.sound]`
  (scratch/kummer-index/axioms.txt).
- No new Tau Ceti module vendored; no vendored file edited.
