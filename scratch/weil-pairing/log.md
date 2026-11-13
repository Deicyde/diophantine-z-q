# weil-pairing results log

- 23:05 start. `lake build ZInQKernel.HDecomp.Objects`: OK (50 s).
- WeilPairing.lean §1-§2 (torsion `tors A n`, `Mu K n = μ_n(K̄)`, `galTors`, `galMu`, `torsMap`,
  `Pairing A B n := tors A n →+ tors B n →+ Mu K n`, `IsPerfect`, `IsAlternating`,
  `IsGalEquivariant`, `pull`; lemmas `add_left/right`, `val_mul_left/right`, `nsmul_left/right`,
  `val_pow_eq_one`, `IsAlternating.skew`, `IsAlternating.pull`, `IsGalEquivariant.pull`,
  `.pull_hom`, `homP_galP`, `torsMap_galTors`, `IsPerfect.left_trivial`, `isPerfect_zero_iff`):
  COMPILES (lake env lean, 5 s, no errors).
