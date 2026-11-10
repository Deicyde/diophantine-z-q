# pd-lean-2 log

- Merged origin/wip/pd-paper (already done at start). Referee report rv-pd-paper: no repairs for files 3-6, 9.
- Abel.lean: thetaS, phiTerm, PhiS; abel_summation, sum_one_div_rpow_le (Bernoulli), abel_partial_sum_le,
  abel_bound (Lemma 5.2(1)), thetaS_le_log4, thetaS_le_log_mul_card, thetaS_le_of_eventually,
  summable_phiTerm, primesRelUpperDensityPos_of_dirichlet (Prop 5.3; no primality hypothesis needed).
  lake build ZInQKernel OK.
- Plan: PropD generic over c : ℕ → ℤ (pd-lean-1 not landed): needs (h1) goodSlopePrime_of_gcd,
  (h2) c p odd, (h3) ∃ e, p = c² + e² for class primes.
- PrimeTail.lean: sum_inv_sq_le_of_primes_gt (3 log4/(L log L), any finite set of primes > L), prime_tail (note form). Abel+Chebyshev instead of dyadic.
- Lattice.lean: ClassMod56, BadSetOf c ℓ, latticePts, card_latticePts_le (8N/ℓ²+[ℓ≤√N]4√N/ℓ), card_badSet_le_latticePts (needs only hrep: p = c p² + e²), sum_card_badSet_large_le (Σ_{ℓ⁴>N} ≤ 20 N^{3/4}).
