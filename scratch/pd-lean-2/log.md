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
- Merged origin/wip/pd-lean-1 (report present). Lattice now uses pd-lean-1's InClass (ClassMod56 removed). Build OK.
- Residues.lean: QL, modSet, ML, crt (ZMod.prodEquivPi), cond, AL, card_AL (=3∏(ℓ-2), via Nat.card + subtypePiEquivPi), totient_ML, deltaL, deltaL_eq, deltaL_ge (L≥4), isUnit_of_mem_AL, CL, mem_CL, phi_CL_lower (Lemma 3.1). Build OK.
- PropD.lean: BadSet, UniformBadBound, cp_rep, TL, goodSlopePrime_of_mem_CL (Lemma 2.1), card_TL_le, eventually_rpow_mul_log_le, exists_L, goodPrimeDensity_of_uniformBadBound. Build OK; axioms propext/choice/Quot.sound.
- Merged origin/wip/pd-sieve (report present). PropDFinal.lean: uniformBadBound_holds (convert + Iff.rfl, decidability instances differ), goodPrimeDensity, goodPrimeAP_of_greenTaoDense'. PropD: goodPrimeAP_of_greenTaoDense_uniformBadBound. Build OK, axioms standard.
- Report .fleet/pd-lean-2.md written. Done.
