/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace (git blob 2e63bf8b6032ed08503db58f5a21a47cfaa90ee9, sha256 388733a3d48c23edcb493a69f0d5459a9868f50eedb9f6914707bcc66ab7a3c9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

open scoped Classical FourierTransform SchwartzMap

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing mixedEmbedding.integerLattice mixedEmbedding.traceForm_mixedSpace_nondegenerate)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (fourierIntegral fourierIntegral_def fourierIntegral_zero fourierIntegral_smul fourierIntegral_add schwartzBruhat mem_schwartzBruhat_of_mem_pureTensorSet zero_mem_schwartzBruhat schwartzBruhat_induction fourierIntegral_pureTensor_eq isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing integrable_of_mem_schwartzBruhat norm_apply_eq_one_of_isGlobalAddChar)
namespace Ws25FStab0
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)

include hψ in

theorem integrable_fourierIntegrand {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    (w : AdeleRing (𝓞 F) F) :
    Integrable (fun v => ψ (-(v * w)) * f v) μ := by
  have hfi : Integrable f μ := integrable_of_mem_schwartzBruhat F μ hf
  refine Integrable.mono' hfi.norm ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((hψ.continuous.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable).mul
      hfi.aestronglyMeasurable
  · rw [norm_mul, norm_apply_eq_one_of_isGlobalAddChar F hψ, one_mul]

variable (hψ_inf : ∀ x : InfiniteAdeleRing F,
    ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))

include hψ_inf in

theorem fourierIntegral_psiV_eq (g : mixedEmbedding.mixedSpace F → ℂ) (w : mixedEmbedding.mixedSpace F) :
    fourierIntegral
        (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
        volume g w
      = VectorFourier.fourierIntegral Real.fourierChar volume
          (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)) g w := by
  rw [fourierIntegral_def, VectorFourier.fourierIntegral]
  congr 1 with v
  have h1 : (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom)) (-(v * w))
      = ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (-(v * w)), 0) := rfl
  rw [h1, hψ_inf, RingEquiv.apply_symm_apply, Circle.smul_def, smul_eq_mul, map_neg,
    Algebra.traceForm_apply]

include hψ hψ_inf in
theorem fstab0_impl {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F := by
  refine schwartzBruhat_induction (F := F) (p := fun f _ => fourierIntegral ψ μ f ∈ schwartzBruhat F)
    ?_ ?_ ?_ ?_ hf
  ·
    intro f hf
    obtain ⟨g, h, hlc, hcs, rfl⟩ := hf

    letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
    haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
    let ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar
    set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
    set ψV : AddChar (mixedEmbedding.mixedSpace F) ℂ :=
      ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp e.symm.toAddMonoidHom) with hψV
    set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
      ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf
    set C : ℂ := ((μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ) with hC

    have hT : ∀ w, fourierIntegral ψ μ (fun x ↦ g (e x.1) * h x.2) w
        = C * fourierIntegral ψV volume g (e w.1) * fourierIntegral ψf ν h w.2 :=
      fun w => fourierIntegral_pureTensor_eq F μ ν hψ.continuous
        (norm_apply_eq_one_of_isGlobalAddChar F hψ) g hlc hcs w

    have hV : fourierIntegral ψV volume g
        = VectorFourier.fourierIntegral Real.fourierChar volume
            (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)) g :=
      funext (fourierIntegral_psiV_eq F hψ_inf g)
    obtain ⟨g₁, hg₁⟩ := SchwartzMap.exists_coe_eq_vectorFourierIntegral
      (volume : Measure (mixedEmbedding.mixedSpace F))
      (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F))
      (mixedEmbedding.traceForm_mixedSpace_nondegenerate F) g

    obtain ⟨hlc', hcs'⟩ :=
      isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing F ν hψ hψ_inf hlc hcs

    refine mem_schwartzBruhat_of_mem_pureTensorSet ⟨C • g₁, fourierIntegral ψf ν h, hlc', hcs', ?_⟩
    funext w
    rw [hT w, SchwartzMap.smul_apply, smul_eq_mul, hg₁, ← hV]
  ·
    show fourierIntegral ψ μ 0 ∈ schwartzBruhat F
    rw [fourierIntegral_zero]; exact zero_mem_schwartzBruhat
  ·
    intro f g hf hg ihf ihg
    show fourierIntegral ψ μ (f + g) ∈ schwartzBruhat F
    have : fourierIntegral ψ μ (f + g) = fourierIntegral ψ μ f + fourierIntegral ψ μ g := by
      funext w
      exact fourierIntegral_add ψ μ w (integrable_fourierIntegrand F μ hψ hf w)
        (integrable_fourierIntegrand F μ hψ hg w)
    rw [this]; exact Submodule.add_mem _ ihf ihg
  ·
    intro c f _ ih
    show fourierIntegral ψ μ (c • f) ∈ schwartzBruhat F
    rw [fourierIntegral_smul]; exact Submodule.smul_mem _ c ih

end NumberField.AdelicFourier.Ws25FStab0

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F :=
  NumberField.AdelicFourier.Ws25FStab0.fstab0_impl F μ hψ hψ_inf hf
