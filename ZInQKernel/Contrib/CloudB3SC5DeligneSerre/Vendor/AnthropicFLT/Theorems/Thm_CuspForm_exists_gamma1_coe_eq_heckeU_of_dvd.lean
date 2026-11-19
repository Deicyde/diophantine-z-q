/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd (git blob 187d1c43d7f57773733725060584c5036788b37e, sha256 489798316e0f9705f05f79e86e0846f5df1d8ef88ecc00b3ba18d0738b8961ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd
    {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ∣ N) (f : CuspForm (Gamma1 N) k) :
    ∃ U : CuspForm (Gamma1 N) k,
      (⇑U : UpperHalfPlane → ℂ) = ModularForm.heckeU k ℓ ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff f (ℓ * n)) ∧
      ∀ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f → CuspForm.HasNebentypus ε U := by
  revert N k ℓ hℓ f
  exact @_root_.P2MW.S_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd.solution
