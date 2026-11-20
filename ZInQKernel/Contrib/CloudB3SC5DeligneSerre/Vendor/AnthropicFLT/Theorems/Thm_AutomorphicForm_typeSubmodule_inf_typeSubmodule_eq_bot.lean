/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot (git blob 34fa0318546786ddc709cf7a37b5ff238ba83c0b, sha256 52097fa693687309a8a98cbac1dca88681089d056f2d6fa56f025d2d45bf83d0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AutomorphicForm.typeSubmodule_inf_typeSubmodule_eq_bot
    {H G : Type*} [Group H] [Group G]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    typeSubmodule ι ρ ⊓ typeSubmodule ι ρ' = ⊥ := by
  revert H G W W' ι ρ ρ' hne
  exact @_root_.P2MW.S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot.solution
