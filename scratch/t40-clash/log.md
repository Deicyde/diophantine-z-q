# t40-clash results log

- 17:47 Reproduced: scratch/t40-clash/Clash2.lean (imports GroupWithZero.Units.Basic then
  Backport.Algebra.Group.Units.Basic) fails: "environment already contains
  'Units.val_mul_zpow_natCast_mul' from ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic".
  Three names clash, not one: TauCeti.mem_range_iff_exists_units_map_eq,
  Units.val_mul_zpow_natCast_mul, Units.val_mul_zpow_neg_natCast_succ_mul (Backport copies are the
  commit-4d91513e generalizations: local monoid hom / DivisionCommMonoid).
