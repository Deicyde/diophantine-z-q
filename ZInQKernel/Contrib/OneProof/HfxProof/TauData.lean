import ZInQKernel.Contrib.OneProof.HfxProof.TwoAdic

/-!
# hfx-proof: the data of an admissible embedding

Task hfx-proof. For squarefree `n ≡ 1, 3 (mod 8)` and an admissible `τ` (`AdmissibleTau`, TYZ L527–534):
* `τ(√−n) = a i + b j + c k` with `a, b, c ∈ ℤ`, `a² + b² + c² = n`, and `4 ∣ c` if `n ≡ 1 (mod 8)`
  (`exists_abc`);
* `τ(O_K) ⊂ ℤ + ℤω`, with `ω = τ(√−n)` if `n ≡ 1 (mod 8)` and `ω = (1 + τ(√−n))/2` if `n ≡ 3 (mod 8)`
  (`tau_span1`, `tau_span3`).
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.HfxProof

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.T21Proof IsDedekindDomain NumberField
open scoped Quaternion
open ZInQ.RouteK.Rank5b

theorem sqrtNeg_mul_self (n : ℕ) : sqrtNeg n * sqrtNeg n = -(n : QNeg n) := by
  ext <;> simp [sqrtNeg]

theorem sqrtNeg_isIntegral (n : ℕ) : IsIntegral ℤ (sqrtNeg n) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [sq, sqrtNeg_mul_self]; simp

/-- `√−n ∈ 𝓞(ℚ(√−n))`. -/
def sqrtNegO (n : ℕ) [NeZero n] : 𝓞 (QNeg n) := ⟨sqrtNeg n, sqrtNeg_isIntegral n⟩

/-- `τ(x) = re x + im x · τ(√−n)`. -/
theorem tau_apply {n : ℕ} (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (x : QNeg n) :
    τ x = ((x.re : ℚ) : ℍ[ℚ]) + x.im • τ (sqrtNeg n) := by
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul x]
  rw [map_add, map_smul, map_smul, map_one, Algebra.smul_def, mul_one]
  rfl

/-- **The coordinates of `τ(√−n)`.** -/
theorem exists_abc {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ)
    (hcl : n % 8 = 1 ∨ n % 8 = 3) :
    ∃ a b c : ℤ, τ (sqrtNeg n) = ⟨0, (a : ℚ), (b : ℚ), (c : ℚ)⟩ ∧ (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (n % 8 = 1 → 4 ∣ c) := by
  rcases hcl with h1 | h3
  · obtain ⟨a, b, c, hn, h4, he⟩ := hτ.2 h1
    exact ⟨a, b, c, he, hn, fun _ => h4⟩
  · obtain ⟨A, B, C, D, e, he⟩ := hτ.1 (sqrtNegO n)
    have hsq : τ (sqrtNeg n) * τ (sqrtNeg n) = -(n : ℍ[ℚ]) := by
      rw [← map_mul, sqrtNeg_mul_self, map_neg, map_natCast]
    change τ (sqrtNeg n) = _ at he
    rw [he] at hsq
    have h0 := congrArg (·.re) hsq
    have h1 := congrArg (·.imI) hsq
    simp at h0 h1
    set r : ℚ := (A : ℚ) - e / 2 with hr
    have hr0 : r = 0 := by
      by_contra hr0
      have hb : (B : ℚ) + e / 2 = 0 := by
        have : 2 * r * ((B : ℚ) + e / 2) = 0 := by linear_combination h1
        rcases mul_eq_zero.mp this with h | h
        · exfalso; apply hr0; linarith
        · exact h
      have h2 := congrArg (·.imJ) hsq
      have h3 := congrArg (·.imK) hsq
      simp at h2 h3
      have hc : (C : ℚ) + e / 2 = 0 := by
        have : 2 * r * ((C : ℚ) + e / 2) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp this with h | h
        · exfalso; apply hr0; linarith
        · exact h
      have hd : (D : ℚ) + e / 2 = 0 := by
        have : 2 * r * ((D : ℚ) + e / 2) = 0 := by linear_combination h3
        rcases mul_eq_zero.mp this with h | h
        · exfalso; apply hr0; linarith
        · exact h
      rw [hb, hc, hd] at h0
      have : (0 : ℚ) ≤ n := by positivity
      nlinarith [sq_nonneg r, sq_pos_of_ne_zero hr0]
    have he2 : (e : ℚ) = 2 * A := by linarith
    refine ⟨B + A, C + A, D + A, ?_, ?_, fun h => by omega⟩
    · rw [he]; ext <;> simp <;> linarith
    · rw [hr0, he2] at h0
      have : ((n : ℤ) : ℚ) = (((B + A) ^ 2 + (C + A) ^ 2 + (D + A) ^ 2 : ℤ) : ℚ) := by
        push_cast; nlinarith
      exact_mod_cast this

/-- `n ≡ 1 (mod 8)`: `τ(O_K) ⊂ ℤ + ℤ τ(√−n)`. -/
theorem tau_span1 {n : ℕ} [NeZero n] (hsq : Squarefree n) (h1 : n % 8 = 1) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (x : 𝓞 (QNeg n)) : ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • τ (sqrtNeg n) := by
  obtain ⟨⟨m, hm⟩, ⟨N, hN⟩⟩ := trace_norm_int x
  set u := (x : QNeg n).re with hu
  set w := (x : QNeg n).im with hw
  have hV : (n : ℚ) * (2 * w) ^ 2 = ((4 * N - m ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [hN, hm]; ring
  obtain ⟨V, hVv⟩ := int_of_sqfree_mul_sq hsq hV
  have hEq : 4 * N = m ^ 2 + (n : ℤ) * V ^ 2 := by
    have : ((4 * N : ℤ) : ℚ) = ((m ^ 2 + (n : ℤ) * V ^ 2 : ℤ) : ℚ) := by
      push_cast; rw [hN, hm, hVv]; ring
    exact_mod_cast this
  have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 1 := by
    have := Nat.div_add_mod n 8; rw [h1] at this; exact_mod_cast this.symm
  rw [hk] at hEq
  obtain ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ := parity_one hEq
  refine ⟨s, t, ?_⟩
  rw [tau_apply]
  have hus : u = s := by push_cast at hm; linarith
  have hwt : w = t := by push_cast at hVv; linarith
  rw [← hu, ← hw, hus, hwt]; norm_cast

/-- `n ≡ 3 (mod 8)`: `τ(O_K) ⊂ ℤ + ℤ ω`, `ω = (1 + τ(√−n))/2`. -/
theorem tau_span3 {n : ℕ} [NeZero n] (hsq : Squarefree n) (h3 : n % 8 = 3) (τ : QNeg n →ₐ[ℚ] ℍ[ℚ])
    (x : 𝓞 (QNeg n)) :
    ∃ m s : ℤ, τ x = (m : ℍ[ℚ]) + (s : ℚ) • ((1 / 2 : ℚ) • (1 + τ (sqrtNeg n))) := by
  obtain ⟨⟨m, hm⟩, ⟨N, hN⟩⟩ := trace_norm_int x
  set u := (x : QNeg n).re with hu
  set w := (x : QNeg n).im with hw
  have hV : (n : ℚ) * (2 * w) ^ 2 = ((4 * N - m ^ 2 : ℤ) : ℚ) := by
    push_cast; rw [hN, hm]; ring
  obtain ⟨V, hVv⟩ := int_of_sqfree_mul_sq hsq hV
  have hEq : 4 * N = m ^ 2 + (n : ℤ) * V ^ 2 := by
    have : ((4 * N : ℤ) : ℚ) = ((m ^ 2 + (n : ℤ) * V ^ 2 : ℤ) : ℚ) := by
      push_cast; rw [hN, hm, hVv]; ring
    exact_mod_cast this
  have hk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 3 := by
    have := Nat.div_add_mod n 8; rw [h3] at this; exact_mod_cast this.symm
  rw [hk] at hEq
  have hpar : ∃ j : ℤ, m - V = 2 * j := by
    rcases parity_three hEq with ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ | ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
    · exact ⟨s - t, by ring⟩
    · exact ⟨s - t, by ring⟩
  obtain ⟨j, hj⟩ := hpar
  refine ⟨j, V, ?_⟩
  rw [tau_apply, ← hu, ← hw]
  have hus : u = m / 2 := by linarith
  have hwt : w = V / 2 := by linarith
  have hjq : (j : ℚ) = (m - V) / 2 := by
    have : ((m - V : ℤ) : ℚ) = 2 * j := by rw [hj]; push_cast; ring
    push_cast at this; linarith
  rw [hus, hwt]
  have e1 : (((m : ℚ) / 2 : ℚ) : ℍ[ℚ]) = ((m : ℚ) / 2) • (1 : ℍ[ℚ]) := by
    ext <;> simp
  have e2 : ((j : ℤ) : ℍ[ℚ]) = (j : ℚ) • (1 : ℍ[ℚ]) := by
    rw [← Quaternion.coe_mul_eq_smul, mul_one]; norm_cast
  rw [e1, e2, hjq]
  module

end ZInQ.Contrib.HfxProof
