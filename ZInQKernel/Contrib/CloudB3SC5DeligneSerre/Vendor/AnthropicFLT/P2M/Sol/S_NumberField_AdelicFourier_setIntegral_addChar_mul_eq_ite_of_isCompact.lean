/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact (git blob 4c9766b08e76cb2fd542aec714687927f679fae2, sha256 dd18b3e7922aeb72b36a1f74395ccce7efde613a1c5b9216f6b38a79f15ac1c9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
namespace AdelicFourier
namespace Ws25OrthK
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
  (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in

theorem setIntegral_comp_add_left_eq [MeasurableAdd (FiniteAdeleRing (𝓞 F) F)]
    (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    {c : FiniteAdeleRing (𝓞 F) F} (hc : c ∈ K) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), g (c + z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), g z ∂ν := by
  have hpre : (fun z : FiniteAdeleRing (𝓞 F) F => c + z) ⁻¹' (K : Set (FiniteAdeleRing (𝓞 F) F))
      = (K : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext z
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => by simpa using K.add_mem (K.neg_mem hc) h, fun h => K.add_mem hc h⟩
  have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) g (K : Set (FiniteAdeleRing (𝓞 F) F))
  rwa [hpre] at h

theorem char_mul_setIntegral_eq (hKm : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) {c : FiniteAdeleRing (𝓞 F) F} (hc : c ∈ K) :
    ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν := by
  calc ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * c) * ψf (ξ * z) ∂ν :=
        (integral_const_mul _ _).symm
    _ = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * (c + z)) ∂ν := by
        refine setIntegral_congr_fun hKm (fun z _ => ?_)
        rw [mul_add, AddChar.map_add_eq_mul]
    _ = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν :=
        setIntegral_comp_add_left_eq ν K (fun z => ψf (ξ * z)) hc

theorem setIntegral_addChar_mul_eq_ite (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 := by
  have hKm : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)) := hK.isClosed.measurableSet
  split_ifs with h
  · rw [setIntegral_congr_fun hKm (fun z hz => h z hz), setIntegral_const]
    simp [Measure.real, Complex.real_smul]
  · have h' : ∃ c ∈ K, ψf (ξ * c) ≠ 1 := by
      by_contra h'
      exact h (fun z hz => by_contra fun hz' => h' ⟨z, hz, hz'⟩)
    obtain ⟨c, hcK, hc⟩ := h'
    have hkey := char_mul_setIntegral_eq ν ψf K hKm ξ hcK
    by_contra hI
    apply hc
    have h1 : ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
        = 1 * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν := by
      rw [hkey, one_mul]
    exact mul_right_cancel₀ hI h1

end NumberField.AdelicFourier.Ws25OrthK

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 :=
  NumberField.AdelicFourier.Ws25OrthK.setIntegral_addChar_mul_eq_ite ν ψf K hK ξ
