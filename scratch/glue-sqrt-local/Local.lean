import Mathlib

/-!
# glue-sqrt-local: the integral closure of `ℤ_p` in a finite extension of `ℚ_p` is local

Through Mathlib's spectral norm (multiplicative and nonarchimedean since `ℚ_p` is complete):
`y` is integral over `ℤ_p` iff `‖y‖_sp ≤ 1`, the units of `S` are the elements of norm `1`, and
the elements of norm `< 1` are closed under addition.
-/

open Polynomial

namespace GlueSqrtLocal

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- `y ∈ L` is integral over `ℤ_p` iff its spectral norm is at most `1`. -/
theorem isIntegral_iff_spectralNorm_le_one (y : L) :
    IsIntegral ℤ_[p] y ↔ spectralNorm ℚ_[p] L y ≤ 1 := by
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

local notation "N" => spectralNorm ℚ_[p] L

theorem spectralNorm_mul' (x y : L) : N (x * y) = N x * N y :=
  (spectralMulAlgNorm ℚ_[p] L).map_mul x y

/-- **The integral closure of `ℤ_p` in a finite extension `L` of `ℚ_p` is a local ring.** -/
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure ℤ_[p] L) := by
  have hle : ∀ x : integralClosure ℤ_[p] L, N (x : L) ≤ 1 := fun x =>
    (isIntegral_iff_spectralNorm_le_one p L x).mp x.2
  have hunit : ∀ x : integralClosure ℤ_[p] L, IsUnit x ↔ N (x : L) = 1 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : N ((u : integralClosure ℤ_[p] L) : L) * N (((u⁻¹ : _ˣ) : integralClosure ℤ_[p] L) : L)
          = 1 := by
        rw [← spectralNorm_mul', ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one,
          spectralNorm_one]
      have a1 := hle u
      have a2 := hle (u⁻¹ : _ˣ)
      have b1 := spectralNorm_nonneg (K := ℚ_[p]) ((u : integralClosure ℤ_[p] L) : L)
      have b2 := spectralNorm_nonneg (K := ℚ_[p]) (((u⁻¹ : _ˣ) : integralClosure ℤ_[p] L) : L)
      nlinarith
    · intro h
      have hx0 : (x : L) ≠ 0 := by
        intro h0; rw [h0, spectralNorm_zero] at h; exact zero_ne_one h
      have hinv : N ((x : L)⁻¹) = 1 := by
        have := spectralNorm_mul' p L (x : L) (x : L)⁻¹
        rw [mul_inv_cancel₀ hx0, spectralNorm_one, h, one_mul] at this
        exact this.symm
      have hint : IsIntegral ℤ_[p] ((x : L)⁻¹) :=
        (isIntegral_iff_spectralNorm_le_one p L _).mpr hinv.le
      refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : integralClosure ℤ_[p] L) ?_
      apply Subtype.ext
      simp [hx0]
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hunit] at ha hb ⊢
  have ha' : N (a : L) < 1 := lt_of_le_of_ne (hle a) ha
  have hb' : N (b : L) < 1 := lt_of_le_of_ne (hle b) hb
  have := isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := L) (a : L) (b : L)
  rw [Subalgebra.coe_add]
  intro hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end GlueSqrtLocal

#print axioms GlueSqrtLocal.isLocalRing_integralClosure
