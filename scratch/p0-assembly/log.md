# p0-assembly log
- Merged origin/wip/p0-bits and origin/wip/p0-good (no conflicts). Copied .lake from main clone.
- Wrote Selmer/Prop0.lean: prop0, classInt_one_eq_two_mul, dvd_of_squarefree_of_odd_primes_dvd,
  exists_classInt_eq, sel2_subset_range_selPair, prop0Statement, certifiedRank_of_certifiedRankSel.
  Compiled first try.
- Main.lean: exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel.
- lake build ZInQKernel OK; check_target.py OK; #print axioms: propext, Classical.choice, Quot.sound.
- Done; report in .fleet/p0-assembly.md.
