# pd-lean-1 log

- Merged origin/wip/pd-paper (already up to date). No rv-pd-paper report yet.
- CharSum.lean: jac, pointCount_eq, jac_sq_mul, jac_zero, sum_quadraticChar_shift_mul (needs p ≠ 2),
  sum_jac_sq (reuses RouteK.Selmer.sum_cubicCharSum_sq), jac_even, jacobsthal,
  four_dvd_pointCount (only p ≠ 2 needed), four_dvd_pointCount_of_mod_four. Compiles.
- Description.lean: InClass, cp, cp_eq, jac_one_eq, quadraticChar_seven, d_mul_dbar,
  pointCount_pair, cp_odd, sq_add_sq_of_nonsquare, exists_sq_add_sq, int_gcd_sub_add_two_mul,
  nat_gcd_eq_of_sub_add, gcd_pointCount_eq, goodSlopePrime_of_gcd, goodSlopePrime_iff,
  mod_four_of_dvd_cp, cp_seventeen, goodSlopePrime_seventeen'. Compiles.
- lake build ZInQKernel: success. #print axioms goodSlopePrime_of_gcd (and _iff, _seventeen',
  jacobsthal, mod_four_of_dvd_cp): [propext, Classical.choice, Quot.sound].
- rv-pd-paper report: F1 (shift_mul needs p ≠ 2) already applied; nothing else for files 1-2.
