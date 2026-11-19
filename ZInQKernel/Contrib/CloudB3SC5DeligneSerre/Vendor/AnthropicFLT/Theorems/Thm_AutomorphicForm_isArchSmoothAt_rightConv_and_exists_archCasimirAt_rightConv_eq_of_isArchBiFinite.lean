/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite (git blob dd2cf19978bfc555690afd0bfb85f81e689280ea, sha256 45a688e148985c2154357d6d05efa9ae67cc606f2e782774fa6273ca90dc0696).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x')
    (hxl : x' ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N)
    (hxt : x' ∈ archCutSubmodule K tys)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    IsArchSmoothAt hw (rightConv K x' α) ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d (rightConv K x' α))) ∧
    (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (rightConv K x' α)))) ∧
    (∃ β : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧
        archCasimirAt hw (rightConv K x' α) = rightConv K x' β) ∧
    archCasimirAt hw (rightConv K x' α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
      archCutSubmodule K tys := by
  revert K D w hw N tys x' hxc hxl hxt α hαf hαb hαU
  exact @_root_.P2MW.S_AutomorphicForm_isArchSmoothAt_rightConv_and_exists_archCasimirAt_rightConv_eq_of_isArchBiFinite.solution
