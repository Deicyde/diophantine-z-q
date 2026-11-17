/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Subgroup_exists_eq_mul_of_index_inf_eq (git blob 1b2b1321005fe6185c17b6025fd16aece7e61de4, sha256 0b465d37193b06ab27430e1c970c19f52e4b98145898a930fb3467bedeb61b96).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.GroupTheory.Index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Subgroup_exists_eq_mul_of_index_inf_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G] (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) : ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by
  revert G H₁ H₂ h g
  exact @_root_.P2MW.S_Subgroup_exists_eq_mul_of_index_inf_eq.solution
