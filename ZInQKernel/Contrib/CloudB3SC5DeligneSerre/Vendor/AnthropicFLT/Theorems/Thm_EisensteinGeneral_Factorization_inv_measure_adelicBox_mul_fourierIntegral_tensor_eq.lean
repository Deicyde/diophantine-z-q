/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq (git blob 1c01bb95e8848e2648bdafa52655d255759a39ee, sha256 74d612e405bfbd4524092e822e1b39399674ae95e8076699965d1a41ce26f96e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier
  IsDedekindDomain

open scoped Classical in

theorem EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (w : AdeleRing (𝓞 F) F) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        fourierIntegral ψ μ (fun x ↦ f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2) w
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (fourierIntegral
              (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
                (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
              MeasureTheory.volume f (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹
              * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν g w.2)) := by
  revert F μ ν ψ f g w
  exact @_root_.P2MW.S_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq.solution
