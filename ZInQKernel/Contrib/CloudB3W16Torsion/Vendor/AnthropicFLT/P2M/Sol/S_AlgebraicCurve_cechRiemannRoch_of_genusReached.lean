/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_cechRiemannRoch_of_genusReached. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_H1_of_genusReached
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_cechRiemannRoch_of_genusReached

set_option autoImplicit false

open AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) := by
  obtain ⟨v₀, hv₀⟩ := h₀
  haveI : Nonempty (Place K F) := ⟨v₀⟩
  haveI : FiniteDimensional K ↥(LSpace D) := finiteDimensional_lSpace (K := K) (F := F) D
  haveI : Module.Finite K (H1 D) := finite_H1_of_genusReached h D
  let e0 := cechH0Equiv hcover D
  let e1 : cechH1 S₀ S₁ D ≃ₗ[K] H1 D :=
    LinearEquiv.ofBijective (cechH1ToH1 hcover D) (cechH1ToH1_bijective h hcover ⟨v₀, hv₀⟩ h₁ D)
  haveI : Module.Finite K (cechH1 S₀ S₁ D) := Module.Finite.equiv e1.symm
  have h0 : Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D := e0.finrank_eq
  have h1 : Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D := by
    rw [e1.finrank_eq, indexOfSpecialty_eq_finrank_H1]
  obtain ⟨-, hidx⟩ := indexOfSpecialty_eq_of_genusReached h D
  refine ⟨LinearEquiv.finiteDimensional e0.symm, inferInstance, h0, h1, ?_, fun hD => ?_⟩
  · rw [h0, h1]; omega
  · have hreach := h.eq_of_ge hD
    have hi0 : Module.finrank K (cechH1 S₀ S₁ D) = 0 := by
      have : (indexOfSpecialty D : ℤ) = 0 := by rw [hidx]; omega
      rw [h1]; exact_mod_cast this
    exact Module.finrank_zero_iff.mp hi0
