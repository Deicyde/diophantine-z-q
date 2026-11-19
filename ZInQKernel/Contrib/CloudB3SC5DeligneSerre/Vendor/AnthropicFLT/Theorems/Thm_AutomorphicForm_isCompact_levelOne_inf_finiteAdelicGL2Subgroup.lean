/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup (git blob 6718b8b19366bae3059a47fea11b7f39c5743bf6, sha256 e539598e0f90963030d7af9d2dbe79deeb012929bade3ef6c177bc6d3537af09).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  revert F N
  exact @_root_.P2MW.S_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup.solution
