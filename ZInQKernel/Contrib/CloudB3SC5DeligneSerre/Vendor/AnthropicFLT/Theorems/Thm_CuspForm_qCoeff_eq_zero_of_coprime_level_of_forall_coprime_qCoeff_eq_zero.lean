/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero (git blob bcb8200bd7ceedf61eb31f9c8097d91182ec954a, sha256 5ac4a65c88f808af2ba629a1d676a862ca616e3a8137074120438f046a419a61).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) : ModularFormClass.qCoeff f n = 0 := by
  revert N k K hK f hf n hn
  exact @_root_.P2MW.S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero.solution
