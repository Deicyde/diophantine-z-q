import Mathlib
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Valuation

/-!
# Integral parameters for the split model

On-the-spot (c), for tex 8462–8465. At an odd prime, lift a sum of
two squares from the residue field. At two, use a square root near one
and a second coordinate of zero or two.
-/

namespace ZInQ.Manuscript.RC.ExplicitSplit

open Polynomial

variable {p : ℕ} [Fact p.Prime]

private theorem unit_natCast {n : ℕ} (hn : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) :=
  PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn))

private theorem odd_sum_sq (hp : p ≠ 2) (s : ℤ_[p]) (hs : IsUnit s) :
    ∃ x y : ℤ_[p], x ^ 2 + y ^ 2 = s := by
  let red : ℤ_[p] →+* ZMod p := PadicInt.toZMod
  obtain ⟨a, b, hab, ha⟩ : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = red s ∧ a ≠ 0 := by
    obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (red s)
    by_cases ha : a = 0
    · refine ⟨b, a, (add_comm _ _).trans hab, ?_⟩
      intro hb
      exact (hs.map red).ne_zero (by simpa [ha, hb] using hab.symm)
    · exact ⟨a, b, hab, ha⟩
  let a₀ : ℤ_[p] := a.val
  let b₀ : ℤ_[p] := b.val
  have ha₀ : red a₀ = a := by simp [a₀, red]
  have hb₀ : red b₀ = b := by simp [b₀, red]
  let F : Polynomial ℤ_[p] := X ^ 2 - C (s - b₀ ^ 2)
  have hev (z : ℤ_[p]) : F.aeval z = z ^ 2 - (s - b₀ ^ 2) := by simp [F]
  have hder : F.derivative.aeval a₀ = 2 * a₀ := by
    simp only [F, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul,
      aeval_C, aeval_X, Nat.reduceSub, pow_one, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  have htwo : (2 : ZMod p) ≠ 0 := by
    have hnp : ¬ p ∣ 2 := fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
    exact fun h => hnp ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h))
  have hnorm : ‖F.aeval a₀‖ < ‖F.derivative.aeval a₀‖ ^ 2 := by
    rw [hev, hder]
    have h₁ : ‖a₀ ^ 2 - (s - b₀ ^ 2)‖ < 1 :=
      (LocalDivision.padic_red_eq_zero_iff _).mp (by
        change red _ = 0
        rw [map_sub, map_sub, map_pow, map_pow, ha₀, hb₀, ← hab]
        ring)
    have h₂ : ‖(2 : ℤ_[p]) * a₀‖ = 1 :=
      le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => by
        have hz := (LocalDivision.padic_red_eq_zero_iff _).mpr h
        change red (2 * a₀) = 0 at hz
        exact (mul_ne_zero htwo ha) (by simpa only [map_mul, map_ofNat, ha₀] using hz))
    simpa [h₂] using h₁
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  rw [hev] at hz
  exact ⟨z, b₀, by rw [sub_eq_zero.mp hz]; ring⟩

private theorem dyadic_square_near_one [Fact (Nat.Prime 2)] (s : ℤ)
    (hs : (8 : ℤ) ∣ 1 - s) : ∃ a : ℤ_[2], (2 * a - 1) ^ 2 = (s : ℤ_[2]) := by
  let F : Polynomial ℤ := X ^ 2 - C s
  have hval : F.aeval (1 : ℤ_[2]) = ((1 - s : ℤ) : ℤ_[2]) := by simp [F]
  have hder : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    simp only [F, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul,
      map_natCast, aeval_X_pow, one_pow, mul_one]
    rfl
  have htwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p (p := 2)
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hval, hder, htwo]
    have hb := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (n := 3)).mpr
      (show ((2 : ℕ) ^ 3 : ℤ) ∣ 1 - s by simpa using hs)
    exact hb.trans_lt (by norm_num)
  obtain ⟨z, hz, hd, -⟩ := hensels_lemma hnorm
  have hz' : z ^ 2 = (s : ℤ_[2]) := sub_eq_zero.mp (by simpa [F] using hz)
  rw [hder, htwo] at hd
  have hdiv : (2 : ℤ_[2]) ∣ z - 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (hd.trans (by norm_num))
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w + 1, ?_⟩
  have he : 2 * (w + 1) - 1 = z := by linear_combination -hw
  rw [he, hz']

/-- Integral parameters for the two split matrix generators. Their doubled/shifted
coordinates also give a zero of the local norm form with third coordinate one. -/
theorem integral_parameters {ell : ℕ} (hell : ell.Prime) (h : ell % 4 = 3) (hp : p ≠ ell) :
    ∃ a b : ℤ_[p], (2 * a - 1) ^ 2 + (2 * b) ^ 2 = -(ell : ℤ_[p]) := by
  by_cases hp₂ : p = 2
  · subst p
    by_cases h8 : ell % 8 = 7
    · obtain ⟨a, ha⟩ := dyadic_square_near_one (-(ell : ℤ)) (by omega)
      exact ⟨a, 0, by simpa using ha⟩
    · obtain ⟨a, ha⟩ := dyadic_square_near_one (-(ell : ℤ) - 4) (by omega)
      refine ⟨a, 1, ?_⟩
      push_cast at ha
      rw [ha]
      ring
  · have hp' : ¬ p ∣ ell := fun hd => hp ((Nat.prime_dvd_prime_iff_eq Fact.out hell).mp hd)
    obtain ⟨x, y, hxy⟩ := odd_sum_sq hp₂ (-(ell : ℤ_[p])) (unit_natCast hp').neg
    have hu : IsUnit (2 : ℤ_[p]) := by
      simpa using unit_natCast (p := p) (fun hd =>
        hp₂ ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd))
    obtain ⟨u, hu⟩ := hu
    have hh : (2 : ℤ_[p]) * ↑u⁻¹ = 1 := by rw [← hu, Units.mul_inv]
    refine ⟨↑u⁻¹ * (x + 1), ↑u⁻¹ * y, ?_⟩
    simpa only [← mul_assoc, hh, one_mul, add_sub_cancel_right] using hxy

#print axioms unit_natCast
#print axioms odd_sum_sq
#print axioms dyadic_square_near_one
#print axioms integral_parameters

end ZInQ.Manuscript.RC.ExplicitSplit
