import PrincipalCuspTransport

/-!
# The period-matched expansion of a principal cusp carrier

The period N expansion before dilation is exactly the period one expansion
after dilation. Positivity, strict periods, and cusp analyticity are derived
from the actual groups and cusp-form structures.
-/

noncomputable section
set_option autoImplicit false

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.PrincipalCuspTransport

/-- The natural level is an actual strict period of its principal group. -/
theorem principal_period (N : ℕ) :
    (N : ℝ) ∈ ((Gamma N).map (mapGL ℝ)).strictPeriods := by
  simp only [strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩

/-- The actual exponential parameter is unchanged when argument and period dilate together. -/
theorem qParam_dilation (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Periodic.qParam (N : ℝ) (TauCeti.scaleGL N • τ : ℍ) =
      Function.Periodic.qParam 1 τ := by
  unfold Function.Periodic.qParam
  rw [TauCeti.coe_scaleGL_smul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  congr 1
  push_cast
  field_simp

/-- The original period-N coefficients converge to the actual transported cusp form. -/
theorem transport_hasSum (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion (N : ℝ) f).coeff m •
      Function.Periodic.qParam 1 τ ^ m) (transport N k f τ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have : Fact (IsCusp OnePoint.infty ((Gamma N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods hN (principal_period N)⟩
  simpa only [qParam_dilation N τ, smul_eq_mul, transport_apply] using
    _root_.ModularForm.hasSum_qExpansion f hN (principal_period N) (TauCeti.scaleGL N • τ)

/-- Dilation transports the principal period-N expansion to the actual period-one expansion. -/
theorem qExpansion_transport (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    qExpansion 1 (transport N k f) = qExpansion (N : ℝ) f := by
  ext m
  exact (_root_.ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map (N ^ 2)) (transport_hasSum N k f) m).symm

end ZInQ.Contrib.HeckePrimeRationality.PrincipalCuspTransport
