import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual cuspidal horizontal mean in Petersson unfolding

Every positive strict period of an actual cusp form has zero horizontal mean
at every positive height. This is derived from its actual zero constant term
and the established integral formula for that coefficient. Weighted and
conjugated strip integrals are consequences, not orthogonality assumptions.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory UpperHalfPlane Complex
open scoped BigOperators MatrixGroups ModularForm ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

/-- The actual cusp function restricted to a horizontal line at positive height. -/
def horizontal {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k)
    (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ := f ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩

/-- Zero constant term of the actual cusp form forces its mean to vanish.
No integration or orthogonality premise is taken. -/
theorem horizontal_mean_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods)
    (y : ℝ) (hy : 0 < y) : ∫ x in 0..h, horizontal f y hy x = 0 := by
  have hc := CuspFormClass.qExpansion_coeff_zero f hh hp
  have hi := ModularFormClass.qExpansion_coeff_eq_intervalIntegral f hh hp 0 hy
  simp only [pow_zero, div_one, one_mul] at hi
  rw [hc] at hi
  have hne : (1 / h : ℂ) ≠ 0 := one_div_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne')
  exact (mul_eq_zero.mp hi.symm).resolve_left hne

/-- The horizontal integral of the conjugate actual cusp also vanishes. -/
theorem horizontal_conj_mean_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods)
    (y : ℝ) (hy : 0 < y) : ∫ x in 0..h, conj (horizontal f y hy x) = 0 := by
  have he := (Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm (horizontal f y hy) :
    (∫ x in 0..h, conj (horizontal f y hy x)) = conj (∫ x in 0..h, horizontal f y hy x))
  change (∫ x in 0..h, conj (horizontal f y hy x)) = conj (∫ x in 0..h, horizontal f y hy x) at he
  rw [he, horizontal_mean_zero f h hh hp y hy, map_zero]

/-- The precise y^(k-2) seed mean used with Lebesgue dx dy is zero. -/
theorem horizontal_weighted_mean_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods)
    (y : ℝ) (hy : 0 < y) :
    ∫ x in 0..h, conj (horizontal f y hy x) * (y : ℂ) ^ (k - 2) = 0 := by
  rw [intervalIntegral.integral_mul_const, horizontal_conj_mean_zero f h hh hp y hy, zero_mul]

/-- Every truncated unfolded strip integral is genuinely zero, with the
constant-term proof supplying the inner vanishing at each positive height. -/
theorem iterated_truncated_strip_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods)
    (S : Set ℝ) (hS : ∀ y ∈ S, 0 < y) :
    ∫ y in S, (if hy : 0 < y then
      ∫ x in 0..h, conj (horizontal f y hy x) * (y : ℂ) ^ (k - 2) else 0) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hyS
  rw [dif_pos (hS y hyS), horizontal_weighted_mean_zero f h hh hp y (hS y hyS)]

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
