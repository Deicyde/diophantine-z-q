import ZInQKernel.Multiplication.Soundness.LocalCongruence

/-!
# The height of an accepted slope

Blueprint: `multiplication/soundness/contact-support.md`.

Assume a six-contact bound `h(u) ≤ A M_S(u)²⁴` on `ℚ \ 𝒞`. For `f = n₁n₂ - n₃ ≠ 0` and a slope
`t` with `Slope(t, ℓ; c₀, c₀n₁, c₀n₂, c₀n₃)`, every odd contact prime of `t` outside `S` divides
`f` to the power `25` (the local congruence), so `M_S(t)²⁵ ∣ f`, and the bound gives
`h(t) ≤ A |f|^{24/25}`. The general form `slope_height_le_of` takes the bound and the properties
of the primes outside `S` (`p > 324`, `p ∤ c₀`, `v_p(ℓ) = 0`) as hypotheses; in the certificate
`S = S_mul` and `A = A_ht`, the bound being `sixContact_at_Smul` (from `SixContactMin`).
-/

namespace ZInQ.Mult



/-- `M_S(t)²⁵ ∣ f` when every odd contact prime outside `S` has `p²⁵ ∣ f`. -/
theorem contactSupport_pow_dvd {S : Finset ℕ} {t : ℚ} {f : ℤ}
    (h : ∀ p : ℕ, p.Prime → p ∉ S → ∀ c ∈ contactSet, 0 < padicValRat p (t - c) →
      Odd (padicValRat p (t - c)) → (p : ℤ) ^ 25 ∣ f) :
    ((contactSupport S t : ℕ) : ℤ) ^ 25 ∣ f := by
  classical
  unfold contactSupport
  rw [Nat.cast_prod, ← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp' hq').mpr hpq)).pow
  · intro p hp
    obtain ⟨hp1, hS, c, hc, hpos, hodd⟩ := Finset.mem_filter.mp hp
    exact h p (Nat.prime_of_mem_primeFactors hp1) hS c hc hpos hodd

/-- If `M²⁵ ∣ f ≠ 0` then `M²⁴ ≤ |f|^{24/25}`. -/
theorem pow_24_le_rpow {M : ℕ} {f : ℤ} (hf : f ≠ 0) (h : ((M : ℤ)) ^ 25 ∣ f) :
    (M : ℝ) ^ 24 ≤ |(f : ℝ)| ^ ((24 : ℝ) / 25) := by
  have hle : ((M : ℤ)) ^ 25 ≤ |f| := Int.le_of_dvd (abs_pos.mpr hf) ((dvd_abs _ _).mpr h)
  have hle' : (M : ℝ) ^ 25 ≤ |(f : ℝ)| := by exact_mod_cast hle
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc (M : ℝ) ^ 24 = ((M : ℝ) ^ 25) ^ ((24 : ℝ) / 25) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hM]; norm_num
    _ ≤ |(f : ℝ)| ^ ((24 : ℝ) / 25) := Real.rpow_le_rpow (by positivity) hle' (by norm_num)

/-- **The height of an accepted slope** (general form), given a six-contact bound
`h(u) ≤ A M_S(u)²⁴` on `ℚ \ 𝒞`. -/
theorem slope_height_le_of {S : Finset ℕ} {A : ℝ} (hA : 0 ≤ A)
    (hest : ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ A * (contactSupport S u : ℝ) ^ 24)
    {t ℓ : ℚ} {c₀ : ℤ}
    (hout : ∀ p : ℕ, p.Prime → p ∉ S → 324 < p ∧ ¬ (p : ℤ) ∣ c₀ ∧ padicValRat p ℓ = 0)
    (n : Fin 3 → ℤ) (hf : n 0 * n 1 - n 2 ≠ 0)
    (hs : SlopePred t ℓ ![c₀, c₀ * n 0, c₀ * n 1, c₀ * n 2]) :
    ((contactSupport S t : ℕ) : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 ∧
      ratHeight t ≤ A * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25) := by
  have ht : t ∉ contactSet := hs.1
  have hdvd := contactSupport_pow_dvd (S := S) fun p hp hpS c hc hpos hodd => by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h1, h2, h3⟩ := hout p hp hpS
    exact local_congruence_of h1 n h2 h3 hs hc hpos hodd
  refine ⟨hdvd, ?_⟩
  calc ratHeight t ≤ A * (contactSupport S t : ℝ) ^ 24 := hest t ht
    _ ≤ A * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25) :=
        mul_le_mul_of_nonneg_left (pow_24_le_rpow hf hdvd) hA

/-- **The height of an accepted slope.** Assume the six-contact estimate (in its minimal form
`SixContactMin`). For `f = n₁n₂ - n₃ ≠ 0` and `t` with `Slope(t, ℓ₀; c_*, c_*n₁, c_*n₂, c_*n₃)`:
`M_{S_mul}(t)²⁵ ∣ f` and `h(t) ≤ A_ht |f|^{24/25}`. -/
theorem slope_height_le (hH : SixContactMin) (n : Fin 3 → ℤ)
    (hf : n 0 * n 1 - n 2 ≠ 0) {t : ℚ} (hs : SlopePred t (Syntax.ell : ℚ) (certShifts n)) :
    ((contactSupport S_mul t : ℕ) : ℤ) ^ 25 ∣ n 0 * n 1 - n 2 ∧
      ratHeight t ≤ (Syntax.Aht : ℝ) * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25) := by
  refine slope_height_le_of (by positivity) (fun u hu => sixContact_at_Smul hH hu)
    (fun p hp hpS => ?_) n hf hs
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h324, hc, -, -⟩ := not_mem_S_mul hp hpS
  exact ⟨h324, by exact_mod_cast hc,
    padicValRat_ell_of_not_mem fun hb => hpS (S_b_subset_S_mul hb)⟩

end ZInQ.Mult
