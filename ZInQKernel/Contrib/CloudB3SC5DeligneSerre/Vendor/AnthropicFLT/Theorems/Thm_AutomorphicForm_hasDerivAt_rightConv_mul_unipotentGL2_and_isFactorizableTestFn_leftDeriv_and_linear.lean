/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear (git blob 420272ef12186bc4cb1a9c47047eff75b36cfec1, sha256 d4f7291e5743e4e05031d242caf4167e6d0b82f5ba2e77badf226763fab1c2d4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped Classical in

theorem AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    (∀ (v : mixedEmbedding.mixedSpace K) (g : AdelicGL2 (𝓞 K) K),
        HasDerivAt (fun t : ℝ => rightConv K φ f (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)))
          (rightConv K φ (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) g) 0) ∧
    (∀ v : mixedEmbedding.mixedSpace K,
        IsFactorizableTestFn K (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) ∧
    (∀ (a b : ℝ) (v w : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
        deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • (a • v + b • w))), 0) * y)) 0 =
          a * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0 +
            b * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • w)), 0) * y)) 0) := by
  revert K φ hcont f hf
  exact @_root_.P2MW.S_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear.solution
