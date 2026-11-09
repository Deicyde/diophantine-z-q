# p0-charsum log

- Setup: .lake/packages symlinked to the main clone's packages (identical manifest).
- Lemma Q (sum_quadraticChar_mul_sub), cubicCharSum, square-class invariance, Jacobsthal identity
  sum_cubicCharSum_sq, Lemma J cubicCharSum_one_sq_le / cubicCharSum_sq_le: proved (compiled).
  J avoids a non-square g: Σ_t S(t²)² = Σ_n (1+χ n) S(n)² ≤ 2 Σ_n S(n)² via quadraticChar_card_sqrts.
- Count eight_mul_fibreCard_ge (8N ≥ q - 15 - |S(d²)|), fibreCard_pos (q ≥ 26), exists_xi_of_card: proved.
- Small primes: eulerNat/xiOK/xiCheckPrime checker on ℕ (Euler's criterion via Nat.pow, GMP in the
  kernel), xiCheck_small by `decide +kernel` (instant); bridge xi_of_xiOK, exists_xi_of_check.
- exists_xi proved; `#print axioms`: propext, Classical.choice, Quot.sound.
- Root module ZInQKernel/RouteK/SelmerCharSum.lean, import added; `lake build ZInQKernel` succeeded.
- Pitfall: in `first | simp [..] | ...`, simp turning the goal into False counts as success;
  use `(simp [..]; done)`. `norm_num` proves ¬ Nat.Prime 4 only with Mathlib.Tactic.NormNum.Prime.
