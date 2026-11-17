/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj (git blob 03080632527e26a003e16bc2ac4fba836b9a49bd, sha256 a5c135060a9f45bd89295111b292a89f417d8f02f832db680ecd4d6a89901eb7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
    (M : ℕ) (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ g' : CuspForm (Gamma1 M) k,
      (∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = -(starRingEnd ℂ (τ : ℂ)) →
        g' τ = starRingEnd ℂ (g τ')) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n) := by
  revert M k g
  exact @_root_.P2MW.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj.solution
