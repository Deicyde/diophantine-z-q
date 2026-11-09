# p0-two log

- Merged origin/wip/p0-local and origin/wip/p0-charsum (no conflict in ZInQKernel.lean). Base build OK.
- Plan: Two.lean, helpers on ℚ₂ norms, witness lemma (k = 1), case split on v₂(x).
  Only `Odd d` is needed (not d ≡ 5 mod 8, not squarefree): proving `loc_two_adic_iff_of_odd`,
  then `loc_two_adic_iff` with `d % 8 = 5`.
- Two.lean written: helpers, loc_two_adic_five (witnesses), loc_two_adic_iff_of_odd, loc_two_adic_iff.
  Compiled after 5 rounds (field_simp normal form 1 - d*4 needed both orientations of the
  nonzero hypotheses; missing import of BadOdd for padic_norm_ne_zpow_odd; one rw on norm_neg).
- lake build ZInQKernel OK; #print axioms: propext, Classical.choice, Quot.sound.
- Profile: no declaration ≥ 100 ms; file ~6 s plus 3.3 s import.
- Report .fleet/p0-two.md written; done.
