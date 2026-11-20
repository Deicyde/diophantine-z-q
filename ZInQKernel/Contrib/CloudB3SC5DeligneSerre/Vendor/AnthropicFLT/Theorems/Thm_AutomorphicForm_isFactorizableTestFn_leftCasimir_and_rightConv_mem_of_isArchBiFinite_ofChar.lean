/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar (git blob 7079a2b0473415c1c69d1eb95419127679e5c345, sha256 5dbfb2f62e6997950960f030ca4692f082d92823656852d24b61edbe6f60fafb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ :=
      fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K (ArchTypeFamily.ofChar K χ) β) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) := by
  revert K D w hw hreal N χ α hαf hαb hαU
  exact @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar.solution
