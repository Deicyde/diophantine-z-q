# cr3-inf log
- Step 1-2: RankInf.lean with InfinitelyManyPoints, infPts_nonsingular, infPtsMap(_bijective),
  infinitelyManyPoints_iff_infinite_points, exists_infinite_order_iff_infinitelyManyPoints.
  Built first try (AddCommGroup.finite_of_fg_isAddTorsion, injective_nsmul_iff_not_isOfFinAddOrder,
  Option.infinite_iff, Equiv.infinite_iff).
- Step 3-4: CertifiedRankInf / TYZInf / TYZClInf / DLInf with *_iff_* equivalences to the Rk forms
  (forall_congr' + exists_infinite_order_iff_infinitelyManyPoints; d ≠ 0 from d % 8 = 5, and for DL
  from D.d₁_mod and slots_d₂_facts). Four main-theorem variants in namespace ZInQ.
  Import in ZInQKernel.lean, 9 print_axioms entries. lake build ZInQKernel OK;
  print_axioms: all 59 entries [propext, Classical.choice, Quot.sound].
