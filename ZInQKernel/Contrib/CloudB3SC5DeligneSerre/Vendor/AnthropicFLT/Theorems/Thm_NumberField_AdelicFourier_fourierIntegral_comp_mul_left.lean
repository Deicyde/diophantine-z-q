/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left (git blob fe497c859c2a1d9a60f6ccbb27e53168c7fa0ca1, sha256 fabec137f30891d319cc3ca62613f5b80997d005c695932b8431a09d3e828628).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.fourierIntegral_comp_mul_left (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by
  revert F μ ψ f a w
  exact @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.solution
