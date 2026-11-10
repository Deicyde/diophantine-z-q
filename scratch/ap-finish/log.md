# ap-finish log
- Worktree had no .lake build; copied packages/build/config (and lean/.lake) from the ap-lean worktree (same base commit c399a64).
- Added ZInQKernel/Hypotheses/GreenTao.lean: ContainsArbitraryAPs, PrimesRelUpperDensityPos, GreenTaoDense, GoodPrimeDensity, goodPrimeAP_of_greenTaoDense (adapted from AudAP.goodPrimeAP_of_greenTao_propD; ℕ progressions with b ≥ 1 need no reversal). Compiled first try.
- Main.lean: imports GreenTao; new exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense; module docstring says 22P_AP needs Proposition D as well as Green–Tao.
- PrimeAP.lean: docstring cites Tao–Ziegler, section 11 (was §10). Statement unchanged.
- lake build ZInQKernel OK; check_target.py OK; #print axioms on both new theorems: propext, Classical.choice, Quot.sound. No sorry.
