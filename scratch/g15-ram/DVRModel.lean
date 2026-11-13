import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Textbook.Different

/-! Development file for `LadicDVRModelZp` (merged into `G15Ram.lean` §2f when done). -/

noncomputable section

namespace G15RamDev

open LadicCond
open PkgI4 (GQp)
open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

/-- `ℤ_p → ℚ_p → F`. -/
@[reducible] def algZpF : Algebra ℤ_[p] F :=
  ((algebraMap ℚ_[p] F).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

attribute [local instance] algZpF

instance towerZpF : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The ring of integers `𝓞_F = integralClosure ℤ_p F`. -/
abbrev OF := integralClosure ℤ_[p] F

theorem norm_eq_spectral (x : F) : ‖(x : Kbar p)‖ = spectralNorm ℚ_[p] F x := by
  rw [spectralNorm.eq_of_tower (L := Kbar p) x, PadicAlgCl.spectralNorm_eq]
  rfl

variable [FiniteDimensional ℚ_[p] F]

/-- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (copied from glue-sqrt-local's
`isIntegral_iff_spectralNorm_le_one`, with the norm of `ℚ̄_p`). -/
theorem isIntegral_iff_norm_le_one (y : F) :
    IsIntegral ℤ_[p] y ↔ ‖(y : Kbar p)‖ ≤ 1 := by
  rw [norm_eq_spectral]
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

theorem mem_OF (y : F) : y ∈ OF F ↔ ‖(y : Kbar p)‖ ≤ 1 := isIntegral_iff_norm_le_one F y

theorem norm_le_one (b : OF F) : ‖((b : F) : Kbar p)‖ ≤ 1 := (mem_OF F b).mp b.2

theorem isUnit_iff_norm (b : OF F) : IsUnit b ↔ ‖((b : F) : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖(((u : OF F) : F) : Kbar p)‖ * ‖((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OF F) : F) * (((u⁻¹ : (OF F)ˣ) : OF F) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      have h2 : (((u : OF F) : F) : Kbar p) * ((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p) = 1 := by
        rw [← IntermediateField.coe_mul, this, IntermediateField.coe_one]
      rw [h2, norm_one]
    have a1 := norm_le_one F u
    have a2 := norm_le_one F (u⁻¹ : (OF F)ˣ)
    have b1 := norm_nonneg ((((u : OF F) : F) : Kbar p))
    have b2 := norm_nonneg (((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p))
    nlinarith
  · intro h
    have hx0 : (b : F) ≠ 0 := by
      intro h0
      rw [h0, IntermediateField.coe_zero, norm_zero] at h
      exact zero_ne_one h
    have hinv : ‖(((b : F)⁻¹ : F) : Kbar p)‖ = 1 := by
      rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    have hint : ((b : F)⁻¹) ∈ OF F := (mem_OF F _).mpr hinv.le
    refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : OF F) ?_
    apply Subtype.ext
    simp [hx0]

theorem isLocalRing_OF : IsLocalRing (OF F) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_norm] at ha hb ⊢
  have ha' : ‖((a : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F a) ha
  have hb' : ‖((b : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F b) hb
  have := IsUltrametricDist.norm_add_le_max ((a : F) : Kbar p) ((b : F) : Kbar p)
  intro hab
  rw [Subalgebra.coe_add, IntermediateField.coe_add] at hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end Model

end G15RamDev
