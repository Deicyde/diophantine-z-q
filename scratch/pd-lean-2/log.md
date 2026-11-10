# pd-lean-2 log

- Merged origin/wip/pd-paper (already done at start). Referee report rv-pd-paper: no repairs for files 3-6, 9.
- Abel.lean: thetaS, phiTerm, PhiS; abel_summation, sum_one_div_rpow_le (Bernoulli), abel_partial_sum_le,
  abel_bound (Lemma 5.2(1)), thetaS_le_log4, thetaS_le_log_mul_card, thetaS_le_of_eventually,
  summable_phiTerm, primesRelUpperDensityPos_of_dirichlet (Prop 5.3; no primality hypothesis needed).
  lake build ZInQKernel OK.
- Plan: PropD generic over c : ℕ → ℤ (pd-lean-1 not landed): needs (h1) goodSlopePrime_of_gcd,
  (h2) c p odd, (h3) ∃ e, p = c² + e² for class primes.
