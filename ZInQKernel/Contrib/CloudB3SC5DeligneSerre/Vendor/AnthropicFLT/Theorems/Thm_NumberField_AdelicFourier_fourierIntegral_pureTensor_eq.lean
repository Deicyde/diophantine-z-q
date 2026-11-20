/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq (git blob 77b558fa64aba55d63d564644c539011ef3c5c69, sha256 6ae3d30109d71bf49b15e00dfafaa0af3e856dfbb5287626a58f0b9461bef391).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.fourierIntegral_pureTensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ) (hψu : ∀ x, ‖ψ x‖ = 1)
    (g : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h)
    (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ
        (fun x ↦ g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) w
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
        * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            MeasureTheory.volume (g : mixedEmbedding.mixedSpace F → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
        * fourierIntegral
            (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν h w.2 := by
  revert F μ ν ψ hψ hψu g h hlc hcs w
  exact @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.solution
