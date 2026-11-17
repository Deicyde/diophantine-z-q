import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 4: the precision rule (H12) and its arithmetic

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 6 "Exact finite precision for one derivative prime", tex lines 3088–3100, and the local
congruences used in paragraph 7, tex 3297–3336.

(H12): for every retained derivative prime, `ρ_T(Fr_ℓ) ≡ J (mod 2^{a+1})`, `J = ρ_T(τ)`,
`J² = I`; then `2^{a+1}` divides `a_ℓ` and `ℓ + 1`, since `tr J = 0` and `det J = -1`.

All statements here are `PROVED`.  The inputs `tr ρ_T(Fr_ℓ) = a_ℓ` and `det ρ_T(Fr_ℓ) = ℓ` (good
`ℓ ≠ 2`; the determinant is the cyclotomic character by the Weil pairing) are `GLUE`, stated as
hypotheses.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Matrix

/-- (H12), tex 3091–3096, `PROVED`, modulo `2^{a+1}`: if the reduction of `ρ_T(Fr_ℓ)` modulo
`2^{a+1}` (trace `a_ℓ`, determinant `ℓ`) equals the reduction of `J = ρ_T(τ)` (trace `0`,
determinant `-1`), then `2^{a+1} ∣ a_ℓ` and `2^{a+1} ∣ ℓ + 1`. -/
theorem H12_divisibility (a : ℕ) (aℓ ℓ : ℤ) (F J : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1))))
    (hFJ : F = J) (htrJ : J.trace = 0) (hdetJ : J.det = -1)
    (htr : F.trace = (aℓ : ZMod (2 ^ (a + 1)))) (hdet : F.det = (ℓ : ZMod (2 ^ (a + 1)))) :
    (2 : ℤ) ^ (a + 1) ∣ aℓ ∧ (2 : ℤ) ^ (a + 1) ∣ ℓ + 1 := by
  subst hFJ
  constructor
  · have h0 : ((aℓ : ℤ) : ZMod (2 ^ (a + 1))) = 0 := by rw [← htr, htrJ]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd aℓ (2 ^ (a + 1))).mp h0
    exact_mod_cast this
  · have h0 : ((ℓ + 1 : ℤ) : ZMod (2 ^ (a + 1))) = 0 := by
      push_cast; rw [← hdet, hdetJ]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (ℓ + 1) (2 ^ (a + 1))).mp h0
    exact_mod_cast this

/-- (H12) over `ℤ₂`, tex 3091–3096, `PROVED`: if `ρ_T(Fr_ℓ) = J + 2^{a+1} X` in `M₂(ℤ₂)` with
`tr ρ_T(Fr_ℓ) = a_ℓ`, `det ρ_T(Fr_ℓ) = ℓ`, `tr J = 0`, `det J = -1`, then `2^{a+1} ∣ a_ℓ` and
`2^{a+1} ∣ ℓ + 1` in `ℤ`. -/
theorem H12_divisibility_Z2 (a : ℕ) (aℓ ℓ : ℤ) (F J X : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hFJ : F = J + (2 : ℤ_[2]) ^ (a + 1) • X) (htrJ : J.trace = 0) (hdetJ : J.det = -1)
    (htr : F.trace = (aℓ : ℤ_[2])) (hdet : F.det = (ℓ : ℤ_[2])) :
    (2 : ℤ) ^ (a + 1) ∣ aℓ ∧ (2 : ℤ) ^ (a + 1) ∣ ℓ + 1 := by
  set φ : ℤ_[2] →+* ZMod (2 ^ (a + 1)) := PadicInt.toZModPow (a + 1)
  have hφ2 : φ ((2 : ℤ_[2]) ^ (a + 1)) = 0 := by
    rw [map_pow, map_ofNat]
    exact_mod_cast ZMod.natCast_self (2 ^ (a + 1))
  apply H12_divisibility a aℓ ℓ (F.map φ) (J.map φ)
  · rw [hFJ]; ext i j; simp [hφ2]
  · rw [Matrix.trace_fin_two]; simp only [Matrix.map_apply]
    rw [← map_add, ← Matrix.trace_fin_two, htrJ, map_zero]
  · rw [Matrix.det_fin_two]; simp only [Matrix.map_apply]
    rw [← map_mul, ← map_mul, ← map_sub, ← Matrix.det_fin_two, hdetJ, map_neg, map_one]
  · rw [Matrix.trace_fin_two]; simp only [Matrix.map_apply]
    rw [← map_add, ← Matrix.trace_fin_two, htr, map_intCast]
  · rw [Matrix.det_fin_two]; simp only [Matrix.map_apply]
    rw [← map_mul, ← map_mul, ← map_sub, ← Matrix.det_fin_two, hdet, map_intCast]

/-- Gap B1-a, tex 2992 and 3089–3093, `PROVED`: (H12) for a retained prime at exponent `a`
(already `2^{a+1}` divides `a_ℓ` and `ℓ + 1`) gives the divisibility `2^a ∣ a_ℓ`, `2^a ∣ ℓ + 1`
needed by (H7) for that prime.  Imposing (H12) on *every* retained prime gives the hypothesis of
(H7) for every `ℓ ∈ I`. -/
theorem B1a_of_H12 (a : ℕ) (aℓ ℓ : ℤ) (h : (2 : ℤ) ^ (a + 1) ∣ aℓ ∧ (2 : ℤ) ^ (a + 1) ∣ ℓ + 1) :
    (2 : ℤ) ^ a ∣ aℓ ∧ (2 : ℤ) ^ a ∣ ℓ + 1 :=
  ⟨(pow_dvd_pow 2 (Nat.le_succ a)).trans h.1, (pow_dvd_pow 2 (Nat.le_succ a)).trans h.2⟩

/-- Matrix model of (H12), tex 3091–3093 and 3163–3165, `PROVED`: if `F = J + c X` with
`tr J = 0`, then `F - (tr F) I = J + c (X - (tr X) I)`, i.e. `F - a_ℓ ≡ J (mod c)`. -/
theorem H12_F_sub_trace {R : Type*} [CommRing R] (c : R) (F J X : Matrix (Fin 2) (Fin 2) R)
    (hFJ : F = J + c • X) (htrJ : J.trace = 0) :
    F - F.trace • (1 : Matrix (Fin 2) (Fin 2) R) = J + c • (X - X.trace • 1) := by
  subst hFJ
  rw [Matrix.trace_add, Matrix.trace_smul, htrJ, zero_add, smul_sub, smul_smul, smul_eq_mul]
  abel

/-- Matrix model of (H12), tex 3184 and 3307–3309, `PROVED`: if `F = J + c X` with `J² = I`, then
`F² = I + c (J X + X J + c X²)`, i.e. `ρ_T(Fr_ℓ)² ≡ I (mod c)`: the Frobenius of `K_λ = ℚ_{ℓ²}`
acts trivially modulo `2^{a+1}`. -/
theorem H12_F_sq {R : Type*} [CommRing R] (c : R) (F J X : Matrix (Fin 2) (Fin 2) R)
    (hFJ : F = J + c • X) (hJ : J * J = 1) :
    F * F = 1 + c • (J * X + X * J + c • (X * X)) := by
  subst hFJ
  rw [add_mul, mul_add, mul_add, hJ, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_add, smul_add, smul_smul]
  abel

/-- tex 3309, `PROVED`: if `2^{a+1} ∣ ℓ + 1` then `q = ℓ² ≡ 1 (mod 2^{a+2})`. -/
theorem q_cong (a : ℕ) (ℓ : ℤ) (h : (2 : ℤ) ^ (a + 1) ∣ ℓ + 1) :
    (2 : ℤ) ^ (a + 2) ∣ ℓ ^ 2 - 1 := by
  obtain ⟨t, ht⟩ := h
  have hℓ : ℓ = 2 ^ (a + 1) * t - 1 := by linarith
  refine ⟨t * (2 ^ a * t - 1), ?_⟩
  rw [hℓ]; ring

/-- tex 3329–3330 and the check "`2^{a+1} ∣ (q-1)/2`", `PROVED`: the transfer shear coefficient
`(q - 1)/2` is divisible by `2^{a+1}`: `q - 1 = 2 · (2^{a+1} s)`. -/
theorem half_q_cong (a : ℕ) (ℓ : ℤ) (h : (2 : ℤ) ^ (a + 1) ∣ ℓ + 1) :
    ∃ s : ℤ, ℓ ^ 2 - 1 = 2 * (2 ^ (a + 1) * s) := by
  obtain ⟨t, ht⟩ := h
  have hℓ : ℓ = 2 ^ (a + 1) * t - 1 := by linarith
  exact ⟨t * (2 ^ a * t - 1), by rw [hℓ]; ring⟩

/-- tex 3171–3174 and 3194–3195 ("the extra bit in (H12) pays exactly for the division by two in
(H18)"), `PROVED`: if `2^{a+1} ∣ ℓ + 1` then `ℓ(ℓ+1)/2 = 2^a · (ℓ · (ℓ+1)/2^{a+1})`. -/
theorem H18_div (a : ℕ) (ℓ : ℤ) (h : (2 : ℤ) ^ (a + 1) ∣ ℓ + 1) :
    ∃ w : ℤ, ℓ * (ℓ + 1) = 2 * (2 ^ a * w) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨ℓ * t, by rw [ht]; ring⟩

/-- tex 3313 ("`-1` is a `2^m`-th power"), `PROVED`: in a finite field `k` with
`2^{m+1} ∣ |k| - 1` (here `k = 𝔽_{ℓ²}` and `ℓ² ≡ 1 (mod 2^{a+2})`, `m ≤ a`), `-1` is a
`2^m`-th power. -/
theorem neg_one_isPow {k : Type*} [Field k] [Fintype k] (m : ℕ)
    (hq : 2 ^ (m + 1) ∣ Fintype.card k - 1) : ∃ x : k, x ^ (2 ^ m) = -1 := by
  -- a generator `g` of the cyclic group `k^×` of order `q - 1 = 2^{m+1} s`; take `x = g^s`
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hcardu : Nat.card kˣ = Fintype.card k - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  have hk : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨s, hs⟩ := hq
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    omega
  have hord : orderOf g = 2 ^ (m + 1) * s := by rw [hg, hcardu, hs]
  refine ⟨((g ^ s : kˣ) : k), ?_⟩
  -- `y = g^{s 2^m}` satisfies `y² = 1` and `y ≠ 1`, hence `y = -1`
  have hy2 : (g ^ (s * 2 ^ m)) * (g ^ (s * 2 ^ m)) = 1 := by
    rw [← pow_add, show s * 2 ^ m + s * 2 ^ m = orderOf g by rw [hord]; ring]
    exact pow_orderOf_eq_one g
  have hy1 : g ^ (s * 2 ^ m) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · positivity
    · rw [hord, pow_succ]
      have : 0 < s * 2 ^ m := by positivity
      nlinarith
  have hval : ((g ^ (s * 2 ^ m) : kˣ) : k) * ((g ^ (s * 2 ^ m) : kˣ) : k) = 1 := by
    rw [← Units.val_mul, hy2, Units.val_one]
  rcases mul_self_eq_one_iff.mp hval with h | h
  · exact absurd (Units.val_eq_one.mp h) hy1
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul]
    exact h

/-- tex 3309 and 3313, `PROVED`: under (H12) at exponent `a` and `m ≤ a`, the residue field
`𝔽_{ℓ²}` satisfies the hypothesis of `neg_one_isPow`. -/
theorem card_cond_of_H12 (a m : ℕ) (hm : m ≤ a) (ℓ : ℕ) (h : (2 : ℤ) ^ (a + 1) ∣ (ℓ : ℤ) + 1) :
    2 ^ (m + 1) ∣ ℓ ^ 2 - 1 := by
  have h1 := q_cong a ℓ h
  have h2 : (2 : ℤ) ^ (m + 1) ∣ (ℓ : ℤ) ^ 2 - 1 := (pow_dvd_pow 2 (by omega)).trans h1
  have hℓ : 1 ≤ ℓ ^ 2 ∨ ℓ = 0 := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (Nat.one_le_pow _ _ h0)
  rcases hℓ with hℓ | rfl
  · have : ((ℓ ^ 2 - 1 : ℕ) : ℤ) = (ℓ : ℤ) ^ 2 - 1 := by push_cast [Nat.cast_sub hℓ]; ring
    rw [← this] at h2
    exact_mod_cast h2
  · simp

/-- tex 3109 (`F² - a_ℓ F + ℓ = 0`), matrix model, `PROVED`: Cayley–Hamilton for `2 × 2` matrices,
`M² - (tr M) M + (det M) I = 0`; on `E[2^a]` the Frobenius matrix `ρ_T(Fr_ℓ)` (trace `a_ℓ`,
determinant `ℓ`) satisfies `F² - a_ℓ F + ℓ = 0`. -/
theorem cayley_hamilton_two {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- tex 3199–3200, `PROVED`: (H12) at a larger exponent implies it at a smaller one, so "the
maximum of the required finite precisions suffices for the whole finite set". -/
theorem H12_mono (a a' : ℕ) (h : a' ≤ a) (x : ℤ) (hx : (2 : ℤ) ^ (a + 1) ∣ x) :
    (2 : ℤ) ^ (a' + 1) ∣ x :=
  (pow_dvd_pow 2 (by omega)).trans hx

end ZInQ.Manuscript.RC.HeegnerAlgebra
