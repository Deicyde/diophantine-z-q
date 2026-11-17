/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn (git blob 26d985ec0fcc65f3549e59b441fab520027ab5ca, sha256 22ac2060f2ce46bd834748cf0eaada662f201e378a04fdc27241077ee6c43765).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) :
    (∀ φ α : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsFactorizableTestFn K α →
      IsArchSmoothAtComplex hw (rightConv K φ α) ∧
        archDerivAtComplex hw d (rightConv K φ α) =
          rightConv K φ (fun y => deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0)) ∧
    (∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa →
        ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
          (fun y : AdelicGL2 (𝓞 K) K =>
              deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) *
                ff (glFin (𝓞 K) K (archFlowAtComplex hw d (-t) * y))) 0) =
            fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
    (∀ φ γ ω : AdelicGL2 (𝓞 K) K → ℂ,
      Continuous φ → IsArchSmoothAtComplex hw φ → Continuous (archDerivAtComplex hw d φ) →
      Continuous γ → HasCompactSupport γ → IsArchSmoothAtComplex hw γ → Continuous (archDerivAtComplex hw d γ) →
      Continuous ω → (∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), ω (y * archFlowAtComplex hw d t) = ω y) →
        rightConv K φ (fun y => archDerivAtComplex hw d γ y * ω y) =
          -rightConv K (archDerivAtComplex hw d φ) fun y => γ y * ω y) := by
  revert K w hw d
  exact @_root_.P2MW.S_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn.solution
