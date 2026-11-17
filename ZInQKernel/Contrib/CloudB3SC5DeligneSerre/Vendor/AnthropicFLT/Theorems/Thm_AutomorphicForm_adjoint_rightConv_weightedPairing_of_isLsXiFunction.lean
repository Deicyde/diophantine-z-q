/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction (git blob c53eb129d57be0dfe111b36539aa10c0c5838d22, sha256 6b627c9ceecb6faf504f9c4b7e9a4895711f55de361348e914090af12a001a37).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hu : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (huc : Continuous u) (hvc : Continuous v)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp (AutomorphicForm.rightConv K u g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, AutomorphicForm.rightConv K u g x * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  revert K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u v hu hv huc hvc hu₂ hv₂ g hg hgc
  exact @_root_.P2MW.S_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction.solution
