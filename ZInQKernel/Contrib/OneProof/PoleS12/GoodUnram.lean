import ZInQKernel.Contrib.OneProof.PoleS12.GoodF.DescentF
import ZInQKernel.Contrib.OneProof.PoleS12.Suff

/-!
# `LocalGoodUnram` is proved

`localGoodUnram : LocalGoodUnram`: at a prime `p ∤ 6ℓ`, every pair `(a, b)` of integers prime to
`p` is a local Kummer class of `E_ℓ` over `ℚ_p`.

S12 (L337–345, L351–355) argues with a formal subgroup: `#E(ℚ_q)/2E(ℚ_q) = 4`, and the image is
contained in the unramified subgroup of order four. The proof here goes through the residue
field instead (ON THE SPOT route, standard): over `𝔽_p` the Kummer map of the reduced curve has
kernel `2E(𝔽_p)`, hence image of order `#E(𝔽_p)[2] = 4`, the whole of `(𝔽_p*/𝔽_p*²)²`
(`GoodF.locM_finite`); a witness `x̄ ∈ 𝔽_p` lifts to `x ∈ ℤ` (the exact root when `x̄` is a root), and
Hensel's lemma (`isSquare_intCast_div_of_residue`, Route K) turns the residue squares into
`p`-adic squares. No point of `E(ℚ_p)` is lifted; only the `x`-coordinate is.
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.RouteK.Selmer ZInQ.Manuscript.PoleRC

theorem lift_isSquare {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q c : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    (hQ : Q = 0 ∨ (Q : ZMod p) ≠ 0) (h : IsSquare ((Q : ZMod p) / (c : ZMod p))) :
    IsSquare ((Q : ℚ_[p]) / c) := by
  rcases hQ with rfl | hQ
  · exact ⟨0, by simp⟩
  have hc' : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hQ' : ¬ (p : ℤ) ∣ Q := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at hQ
  refine isSquare_intCast_div_of_residue hp2 hQ' hc ?_
  obtain ⟨r, hr⟩ := h
  refine ⟨r * c, ?_⟩
  push_cast
  rw [div_eq_iff hc'] at hr
  rw [hr]; ring

/-- **`LocalGoodUnram` holds.** -/
theorem localGoodUnram : LocalGoodUnram := by
  intro ℓ p hp a b hsf hnd ha hb
  have hp2 : p ≠ 2 := by rintro rfl; exact hnd (Dvd.intro (3 * ℓ) (by ring))
  have hp3 : p ≠ 3 := by rintro rfl; exact hnd (Dvd.intro (2 * ℓ) (by ring))
  have hpl : ¬ p ∣ ℓ := fun h => hnd (Dvd.dvd.mul_left h 6)
  have hz : ∀ n : ℕ, n.Prime → n ≠ p → ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n hn hne h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hne ((Nat.prime_dvd_prime_iff_eq hp.out hn).mp h).symm
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hz 2 Nat.prime_two (Ne.symm hp2)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast hz 3 Nat.prime_three (Ne.symm hp3)
  have hℓ : ((ℓ : ℕ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have ha' : (a : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hb' : (b : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hloc := GoodF.locM_finite (F := ZMod p) hc h2 h3 hℓ ha' hb'
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  rcases hloc with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · left
    exact ⟨isSquare_intCast_of_residue hp2 ha hsa, isSquare_intCast_of_residue hp2 hb hsb⟩
  right
  -- the integer lift of `x`, exact at the roots
  classical
  set L : ℤ := (ℓ : ℤ)
  have hLc : ((L : ℤ) : ZMod p) = ((ℓ : ℕ) : ZMod p) := by simp [L]
  obtain ⟨X, hX, hQ1, hQ2, hQ3⟩ : ∃ X : ℤ, (X : ZMod p) = x ∧
      (X + 3 * L = 0 ∨ ((X + 3 * L : ℤ) : ZMod p) ≠ 0) ∧
      (X - L = 0 ∨ ((X - L : ℤ) : ZMod p) ≠ 0) ∧ (X = 0 ∨ ((X : ℤ) : ZMod p) ≠ 0) := by
    have h4 : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    by_cases hx0 : x = 0
    · refine ⟨0, by simp [hx0], Or.inr ?_, Or.inr ?_, Or.inl rfl⟩
      · push_cast; rw [hLc, zero_add]; exact mul_ne_zero h3 hℓ
      · push_cast; rw [hLc, zero_sub]; exact neg_ne_zero.mpr hℓ
    by_cases hx1 : x = (ℓ : ZMod p)
    · refine ⟨L, by rw [hLc, hx1], Or.inr ?_, Or.inl (sub_self L), Or.inr ?_⟩
      · push_cast; rw [hLc, show (ℓ : ZMod p) + 3 * ℓ = 4 * ℓ by ring]; exact mul_ne_zero h4 hℓ
      · rw [hLc]; exact hℓ
    by_cases hx3 : x = -3 * (ℓ : ZMod p)
    · refine ⟨-3 * L, by push_cast; rw [hLc, hx3], Or.inl (by ring), Or.inr ?_, Or.inr ?_⟩
      · push_cast; rw [hLc, show -3 * (ℓ : ZMod p) - ℓ = -(4 * ℓ) by ring]
        exact neg_ne_zero.mpr (mul_ne_zero h4 hℓ)
      · push_cast; rw [hLc, neg_mul]; exact neg_ne_zero.mpr (mul_ne_zero h3 hℓ)
    · refine ⟨(x.val : ℤ), by simp, Or.inr ?_, Or.inr ?_, Or.inr ?_⟩
      · push_cast; rw [ZMod.natCast_zmod_val, hLc]
        intro h; exact hx3 (by linear_combination h)
      · push_cast; rw [ZMod.natCast_zmod_val, hLc]; exact sub_ne_zero.mpr hx1
      · push_cast; rw [ZMod.natCast_zmod_val]; exact hx0
  refine ⟨(X : ℚ_[p]), ?_, ?_, ?_⟩
  · have := lift_isSquare hp2 ha hQ1 (by push_cast; rw [hX, hLc]; exact h₁)
    push_cast at this; simpa [L] using this
  · have := lift_isSquare hp2 hb hQ2 (by push_cast; rw [hX, hLc]; exact h₂)
    push_cast at this; simpa [L] using this
  · have hab : ¬ (p : ℤ) ∣ a * b := fun h => (hpZ.dvd_or_dvd h).elim ha hb
    have := lift_isSquare hp2 hab hQ3 (by push_cast; rw [hX]; exact h₃)
    push_cast at this; exact this

end ZInQ.Manuscript.PoleS12
