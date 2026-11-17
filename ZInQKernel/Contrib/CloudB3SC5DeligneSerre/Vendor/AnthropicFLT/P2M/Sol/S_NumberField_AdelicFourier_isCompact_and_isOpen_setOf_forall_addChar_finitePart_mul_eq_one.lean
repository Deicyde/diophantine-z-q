/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one (git blob 78e2385f0cb0415151b34281df8705e516b83d14, sha256 ba6dd01d4742de2c409ac77abf2774de931634cfdbe08275c52213c4b5466c8d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual)
namespace Ws25
namespace AnnCpt
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y + z ∈ integralFiniteAdeles (𝓞 F) F := fun v => add_mem (hy v) (hz v)

theorem mul_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y * z ∈ integralFiniteAdeles (𝓞 F) F := fun v => mul_mem (hy v) (hz v)

theorem algebraMap_coe_mem_integralFiniteAdeles (q : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F q) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => algebraMap_mem_adicCompletionIntegers (𝓞 F) F v q

theorem continuous_apply_zero {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    Continuous fun x : FiniteAdeleRing (𝓞 F) F => ψ (0, x) :=
  hψ.continuous.comp (continuous_const.prodMk continuous_id)

theorem isCompact_and_isOpen
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F |
          ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by

  have hann :=
    NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
      F hψ hψ_inf
  set A : Set (FiniteAdeleRing (𝓞 F) F) :=
    {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} with hA
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  have hmemA : ∀ w, w ∈ A ↔ ∃ r : F, r ∈ D ∧ w - ι r ∈ integralFiniteAdeles (𝓞 F) F :=
    fun w => hann w

  have hclosed : IsClosed A := by
    have hcont : ∀ z : FiniteAdeleRing (𝓞 F) F, Continuous fun w => ψ (0, w * z) := fun z =>
      (continuous_apply_zero hψ).comp (continuous_id.mul continuous_const)
    have : A = ⋂ z ∈ integralFiniteAdeles (𝓞 F) F, {w | ψ (0, w * z) = 1} := by
      ext w; simp only [hA, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun z _ => isClosed_eq (hcont z) continuous_const

  obtain ⟨a, ha0, ha⟩ := D.isFractional
  have ha0' : (algebraMap (𝓞 F) F a) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha0

  have hsub : A ⊆ (fun z => ι (algebraMap (𝓞 F) F a)⁻¹ * z) '' integralFiniteAdeles (𝓞 F) F := by
    intro w hw
    obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw

    obtain ⟨c, hc⟩ : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = a • r := ha r hr
    refine ⟨ι (algebraMap (𝓞 F) F a) * w, ?_, ?_⟩
    · have hsplit : ι (algebraMap (𝓞 F) F a) * w
          = ι (algebraMap (𝓞 F) F c) + ι (algebraMap (𝓞 F) F a) * (w - ι r) := by
        rw [hc, Algebra.smul_def, map_mul, mul_sub]; abel
      rw [hsplit]
      exact add_mem_integralFiniteAdeles (algebraMap_coe_mem_integralFiniteAdeles c)
        (mul_mem_integralFiniteAdeles (algebraMap_coe_mem_integralFiniteAdeles a) hwr)
    · show ι (algebraMap (𝓞 F) F a)⁻¹ * (ι (algebraMap (𝓞 F) F a) * w) = w
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0', map_one, one_mul]
  have hcompact : IsCompact A :=
    ((isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)).of_isClosed_subset
      hclosed hsub

  have hopen : IsOpen A := by
    refine isOpen_iff_forall_mem_open.mpr fun w hw => ?_
    obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw
    refine ⟨(fun z => ι r + z) '' integralFiniteAdeles (𝓞 F) F, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hmemA _).mpr ⟨r, hr, by rwa [add_sub_cancel_left]⟩
    · exact isOpenMap_add_left (ι r) _ (isOpen_integralFiniteAdeles F)
    · exact ⟨w - ι r, hwr, add_sub_cancel (ι r) w⟩
  exact ⟨hcompact, hopen⟩

end NumberField.AdelicFourier.Ws25.AnnCpt

open NumberField.AdelicFourier.Ws25.AnnCpt in
theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} :=
  isCompact_and_isOpen hψ hψ_inf

end
