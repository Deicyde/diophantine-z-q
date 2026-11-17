/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div (git blob 7efba7338ff136fed7d26ed2843c94653d710158, sha256 b7caf3fd63e2e31a5985e95125402a7d03ab2d719af22dd7bb32c5ee9bdfbadd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓN : ℓ ∣ N) (hℓ : ℓ ∣ N / ℓ)
    (ε' : DirichletCharacter ℂ (N / ℓ)) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hℓN) ε') f) :
    ∃ h : CuspForm (Gamma1 (N / ℓ)) k,
      (⇑h : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      CuspForm.HasNebentypus ε' h := by
  revert N k ℓ hℓN hℓ ε' f hf
  exact @_root_.P2MW.S_CuspForm_exists_gamma1_div_coe_eq_heckeU_of_dvd_div.solution
