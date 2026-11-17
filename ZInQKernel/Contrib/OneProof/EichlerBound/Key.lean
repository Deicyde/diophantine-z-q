import ZInQKernel.Contrib.OneProof.EichlerBound.Crit

/-! eichler-bound, part B4: **no bad primes** for two optimal embeddings of the same type at `2` and `3`:
* `ℓ ∤ 6`: the minor certificate and a descent on the minors of two elements of `J ∩ 𝒪`;
* `ℓ ∣ 6`: `P_ℓ = π𝒪` and conjugation by `π` acting as the quaternion conjugation modulo `P_ℓ`.
No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

/-! ### Primes `ℓ ∤ 6` -/

/-- The sum of the absolute values of the `2 × 2` minors of two coordinate vectors. -/
def minorSum (a b : Fin 4 → ℤ) : ℕ := ∑ i, ∑ j, (a i * b j - a j * b i).natAbs

theorem minorSum_scale {ℓ : ℤ} {a b a' b' : Fin 4 → ℤ}
    (h : ∀ i j, a i * b j - a j * b i = ℓ * (a' i * b' j - a' j * b' i)) :
    minorSum a b = ℓ.natAbs * minorSum a' b' := by
  unfold minorSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h i j, Int.natAbs_mul]

theorem prop_of_minors {a b : Fin 4 → ℤ} (ha : a ≠ 0) (h : ∀ i j, a i * b j - a j * b i = 0) :
    ∃ q : ℚ, ofInt b = q • ofInt a := by
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc; push Not at hc; exact ha (funext hc)
  obtain ⟨q, hq⟩ : ∃ q : ℚ, ∀ j, (b j : ℚ) = q * a j := by
    refine ⟨b i0 / a i0, fun j => ?_⟩
    have := h i0 j
    have hi0' : (a i0 : ℚ) ≠ 0 := by exact_mod_cast hi0
    field_simp
    have : (a i0 : ℚ) * b j = a j * b i0 := by exact_mod_cast (sub_eq_zero.mp this)
    linarith
  refine ⟨q, ?_⟩
  ext <;> simp [ofInt, hq] <;> ring

include Bs in
/-- **No bad prime `ℓ ∤ 6`.** -/
theorem not_bad_coprime (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) {ℓ : ℤ} (hℓ : Prime ℓ)
    (h6 : ¬ ℓ ∣ 6) : ¬ Bad Ψ Φ ℓ := by
  intro hB
  have hB' := bad'_of_bad Bs hk hℓ.ne_zero hB
  have hℓ0 := hℓ.ne_zero
  have hℓ2 : 2 ≤ ℓ.natAbs := by
    rcases Nat.lt_or_ge ℓ.natAbs 2 with h | h
    · exfalso
      interval_cases hh : ℓ.natAbs
      · exact hℓ0 (Int.natAbs_eq_zero.mp hh)
      · exact hℓ.not_unit (Int.isUnit_iff_natAbs_eq.mpr hh)
    · exact h
  -- a starting pair with a nonzero minor
  obtain ⟨c0, hc0, hne⟩ := exists_Jo Bs hk Ψ Φ
  obtain ⟨a0, ha0⟩ := hc0.1
  have hd0 := Jo_mul_right hc0 Bs.mem
  obtain ⟨b0, hb0⟩ := hd0.1
  have hex : ∃ m : ℕ, m ≠ 0 ∧ ∃ a b : Fin 4 → ℤ, ofInt a ∈ Jo Ψ Φ ∧ ofInt b ∈ Jo Ψ Φ ∧
      minorSum a b = m := by
    refine ⟨minorSum a0 b0, ?_, a0, b0, ha0 ▸ hc0, hb0 ▸ hd0, rfl⟩
    intro h0
    have hall : ∀ i j, a0 i * b0 j - a0 j * b0 i = 0 := by
      intro i j
      have := (Finset.sum_eq_zero_iff.mp ((Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)) j
        (Finset.mem_univ _))
      exact Int.natAbs_eq_zero.mp this
    have ha0' : a0 ≠ 0 := by rintro rfl; exact hne (by rw [ha0, ofInt_zero])
    obtain ⟨q, hq⟩ := prop_of_minors ha0' hall
    rw [← ha0, ← hb0] at hq
    apply emb_omega_notRat Bs Ψ q
    have := congrArg (fun x => qinv c0 * x) hq
    rw [qinv_mul_cancel_left hne, mul_smul_comm, qinv_mul hne, ← coe_mul_eq_smul, mul_one] at this
    exact this
  classical
  obtain ⟨hm0, a, b, ha, hb, hab⟩ := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ (m ≠ 0 ∧ ∃ a b : Fin 4 → ℤ, ofInt a ∈ Jo Ψ Φ ∧ ofInt b ∈ Jo Ψ Φ ∧
      minorSum a b = m) := fun m hm => Nat.find_min hex hm
  have hdiv := minor_dvd hℓ h6 a b (hB _ ha _ hb) (hB' _ ha _ hb)
  -- the descent: a pair with minors divided by `ℓ`
  have descent : ∀ a' b' : Fin 4 → ℤ, ofInt a' ∈ Jo Ψ Φ → ofInt b' ∈ Jo Ψ Φ →
      (∀ i j, a i * b j - a j * b i = ℓ * (a' i * b' j - a' j * b' i)) → False := by
    intro a' b' ha' hb' hrel
    have hs := minorSum_scale hrel
    rw [hab] at hs
    apply hmin (minorSum a' b') _ ⟨_, a', b', ha', hb', rfl⟩
    · rw [hs]
      have : minorSum a' b' ≠ 0 := by intro h0; rw [h0, mul_zero] at hs; exact hm0 hs
      have : 0 < minorSum a' b' := Nat.pos_of_ne_zero this
      nlinarith
    · intro h0; rw [h0, mul_zero] at hs; exact hm0 hs
  by_cases hall : ∀ i, ℓ ∣ a i
  · choose a' ha'e using hall
    have hmem : ofInt a' ∈ Jo Ψ Φ := by
      have := Jo_div hℓ0 ha ((LO_ofInt_iff ℓ a).2 (fun i => ⟨a' i, ha'e i⟩))
      have e : ofInt a = ofInt (fun i => ℓ * a' i) := congrArg ofInt (funext ha'e)
      rwa [e, ofInt_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hℓ0), one_smul] at this
    exact descent a' b hmem hb (fun i j => by rw [ha'e i, ha'e j]; ring)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hcop : IsCoprime ℓ (a i) := (Irreducible.coprime_iff_not_dvd hℓ.irreducible).mpr hi
    obtain ⟨v, u, huv⟩ := hcop
    set m' := u * b i
    have hdj : ∀ j, ℓ ∣ b j - m' * a j := by
      intro j
      have h1 : ℓ ∣ a i * (b j - m' * a j) := by
        have e : a i * (b j - m' * a j) = (a i * b j - a j * b i) + ℓ * (v * b i * a j) := by
          have : u * a i = 1 - v * ℓ := by linarith
          simp only [m']; linear_combination (-(b i * a j)) * this
        rw [e]; exact dvd_add (hdiv i j) (dvd_mul_right _ _)
      rcases hℓ.dvd_or_dvd h1 with h | h
      · exact absurd h hi
      · exact h
    choose b' hb'e using hdj
    have hmem : ofInt b' ∈ Jo Ψ Φ := by
      have hsub := Jo_sub hb (Jo_zsmul ha m')
      have hLO : LO ℓ (ofInt b - (m' : ℚ) • ofInt a) := by
        rw [← ofInt_smul, ofInt_sub, LO_ofInt_iff]
        intro j; exact ⟨b' j, by simp [hb'e j]⟩
      have := Jo_div hℓ0 hsub hLO
      have e : ofInt b - (m' : ℚ) • ofInt a = ofInt (fun j => ℓ * b' j) := by
        rw [← ofInt_smul, ofInt_sub]; congr 1; funext j; simp [hb'e j]
      rwa [e, ofInt_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hℓ0), one_smul] at this
    exact descent a b' ha hmem (fun i' j => by
      have e1 := hb'e i'; have e2 := hb'e j
      linear_combination (a i') * e2 - (a j) * e1)

end Emb

end EichlerBound
