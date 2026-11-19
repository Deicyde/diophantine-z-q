/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles (git blob eca9547068013c5d539def7b11bce8ed3b364438, sha256 6f95679f3743bdf0b15383fdaabce1355dd2768b4f8f581a559b34b58231f065).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors
theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (u : FiniteAdeleRing (𝓞 F) F) :
    (∀ w : FiniteAdeleRing (𝓞 F) F,
        (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1) → ψ (0, u * w) = 1)
      ↔ u ∈ integralFiniteAdeles (𝓞 F) F := by
  revert F ψ hψ hψ_inf u
  exact @_root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.solution
