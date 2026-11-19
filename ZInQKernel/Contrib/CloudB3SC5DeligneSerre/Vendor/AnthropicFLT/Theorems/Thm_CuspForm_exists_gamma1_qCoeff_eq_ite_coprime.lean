/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime (git blob 9d1df0c91cf6138861043b90926ce4e7aa3c1c15, sha256 2473c143409ff934d59cd68f4adb2665d45da4f0a2b33840d97e037733993851).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup

theorem CuspForm.exists_gamma1_qCoeff_eq_ite_coprime (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0) (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 := by
  revert N k f Q hQ M hM
  exact @_root_.P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.solution
