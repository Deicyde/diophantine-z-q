
theorem lemmaN2 {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) :
    ∃ X : G.M, G.P n =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L (n / e) • G.Z e + (2 : ℤ) • X := by
  have hn0 : n ≠ 0 := by omega
  have hnD : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  have hP := n2_P_eq G n hnD (Or.inl hn)
  have hw : ∀ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
      ∃ w : GaussianInt, n2_c G.ε L e n = (L (n / e) : GaussianInt) + 2 * w := by
    intro e he
    obtain ⟨hen, he8⟩ := Finset.mem_filter.mp he
    have h := n2_c_mod G hsq hL1 he8 n hnD (Or.inl hn)
    rw [ite_eq_left (Nat.dvd_of_mem_divisors hen), n2_phi, ite_eq_right (by omega), one_mul] at h
    have h0 : n2_π (n2_c G.ε L e n - (L (n / e) : GaussianInt)) = 0 := by
      rw [map_sub, h, map_intCast, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, by linear_combination hw⟩
  choose! w hw using hw
  refine ⟨∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), w e • G.Z e, ?_⟩
  rw [hP, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hw e he, add_smul, Int.cast_smul_eq_zsmul, mul_smul, two_smul, two_smul]

end ZInQ.PropN
