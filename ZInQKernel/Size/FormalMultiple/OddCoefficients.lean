import ZInQKernel.Size.FormalMultiple.ReductionOrders

/-!
# Rational coordinates at odd primes

Blueprint: `size/formal-multiple/odd-coefficient-extraction.md`.

Let `p` be an odd prime and `u = u₀ + u₁ s ∈ K₀`. If `v_π(u) ≥ k` at every prime `π ∣ p` of
`ℤ[s]` (with `v_π(0) = ∞`), then `v_p(u₀) ≥ k` and `v_p(u₁) ≥ k` (with `v_p(0) = ∞`)
(`padicValRat_coords_ge`).

Proof: conjugation permutes the primes above `p` (`v_{σπ}(u) = v_π(σu)`), so `σu` satisfies
the same bounds; `u₀ = (u + σu)/2`, `u₁ = (u - σu)/(2s)` with `v_π(2) = v_π(s) = 0`, and
`v_π(c) = v_p(c)` for `c ∈ ℚ` (`p` is unramified).
-/

namespace ZInQ.Size

open QuadraticAlgebra

variable {p : ℕ} [hp : Fact p.Prime]

theorem not_dvd_sqrt2Z_of_dvd_odd (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) :
    ¬π ∣ sqrt2Z := fun h =>
  not_dvd_two_of_dvd_odd hp2 hπ hπp (h.trans ⟨sqrt2Z, by rw [two_eq_sqrt2Z_sq, sq]⟩)

theorem vp_two_of_dvd_odd (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) :
    vp π (2 : K0) = 0 := by
  have : (2 : K0) = Zs.toK0 2 := (map_ofNat _ 2).symm
  rw [this, vp_eq_zero_iff hπ (by decide)]
  exact not_dvd_two_of_dvd_odd hp2 hπ hπp

theorem vp_sqrt2_of_dvd_odd (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π) (hπp : π ∣ (p : Zs)) :
    vp π sqrt2 = 0 := by
  rw [← toK0_sqrt2Z, vp_eq_zero_iff hπ (by decide)]
  exact not_dvd_sqrt2Z_of_dvd_odd hp2 hπ hπp

theorem re_mul_two (u : K0) : (u.re : K0) * 2 = u + star u := by
  ext <;> simp [K0.star_eq']
  ring

theorem im_mul_two_sqrt2 (u : K0) : (u.im : K0) * (2 * sqrt2) = u - star u := by
  ext <;> simp [K0.star_eq', sqrt2]
  ring

/-- **Rational coordinates at odd primes.** If `v_π(u) ≥ k` at every prime `π ∣ p` of `ℤ[s]`
(`p` an odd prime), then `v_p(u₀) ≥ k` and `v_p(u₁) ≥ k` for the nonzero rational coordinates
of `u = u₀ + u₁ s`. -/
theorem padicValRat_coords_ge (hp2 : p ≠ 2) (k : ℤ) (u : K0)
    (hu : ∀ π : Zs, ∀ hπ : Prime π, π ∣ (p : Zs) → (k : WithTop ℤ) ≤ Mult.vP π hπ u) :
    (u.re ≠ 0 → k ≤ padicValRat p u.re) ∧ (u.im ≠ 0 → k ≤ padicValRat p u.im) := by
  obtain ⟨π, hπ, hπp⟩ := Mult.exists_prime_dvd_natCast p
  have hσ : Prime (star π) := Mult.prime_star hπ
  have hσp : star π ∣ (p : Zs) := by
    have := (Mult.star_pow_dvd_iff (π := π) (a := (p : Zs)) 1).mpr (by simpa using hπp)
    simpa using this
  have h1 : VGe π k u := (Mult.le_vP_iff hπ u k).mp (hu π hπ hπp)
  have h2 : VGe π k (star u) := by
    rcases (Mult.le_vP_iff hσ u k).mp (hu _ hσ hσp) with h | h
    · left; rw [h, star_zero]
    · right; rwa [Mult.vp_star hπ] at h
  have hv2 := vp_two_of_dvd_odd hp2 hπ hπp
  have hvs := vp_sqrt2_of_dvd_odd hp2 hπ hπp
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hre : (u.re : K0) = (u + star u) / 2 := by
      rw [← re_mul_two, mul_div_cancel_right₀ _ two_ne_zero]
    have := (h1.add hπ h2).div hπ (y := (2 : K0)) two_ne_zero
    rw [hv2, sub_zero, ← hre] at this
    rw [vge_iff (Rat.cast_ne_zero.mpr h0), Mult.vp_ratCast hp2 hπ hπp] at this
    exact this
  · have h2s : (2 * sqrt2 : K0) ≠ 0 := mul_ne_zero two_ne_zero sqrt2_ne_zero
    have him : (u.im : K0) = (u - star u) / (2 * sqrt2) := by
      rw [← im_mul_two_sqrt2, mul_div_cancel_right₀ _ h2s]
    have := (h1.sub hπ h2).div hπ h2s
    rw [vp_mul hπ two_ne_zero sqrt2_ne_zero, hv2, hvs, add_zero, sub_zero, ← him] at this
    rw [vge_iff (Rat.cast_ne_zero.mpr h0), Mult.vp_ratCast hp2 hπ hπp] at this
    exact this

end ZInQ.Size
