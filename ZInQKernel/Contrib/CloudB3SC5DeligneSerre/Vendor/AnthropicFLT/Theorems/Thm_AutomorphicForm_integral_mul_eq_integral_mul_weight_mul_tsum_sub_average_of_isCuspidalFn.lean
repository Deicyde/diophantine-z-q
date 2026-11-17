/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn (git blob 6ba92e5b2f7eec752899e42906a0527729937a9e, sha256 cdcf3a30951d3b8f486e924715b56345865efcbcce770fcbbe8b19c996d02b8f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm MeasureTheory
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)), c ∈ tsupport f →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) *
        (unipotentGL2 t * x * c)) = 1) :
    ∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ y, φ y * (w y : ℂ) *
          ((∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
            - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  revert K φ f x hφN hφi hφc hf hfs w hw hw0 hw1
  exact @_root_.P2MW.S_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn.solution
