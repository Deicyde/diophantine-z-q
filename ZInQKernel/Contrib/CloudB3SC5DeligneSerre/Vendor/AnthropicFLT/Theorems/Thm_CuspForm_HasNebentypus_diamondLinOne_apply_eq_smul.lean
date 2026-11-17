/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul (git blob 0e16b1bebfbe865307b501483169489a8b9eabbe, sha256 d288dbfd56a05e7276838381457bb6942a53f2d0bad81d94e80ddba69aa3f469).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_Gamma1HeckeOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul {M : ℕ} {k : ℤ}
    {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.HasNebentypus ε g) {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d g = ε (d : ZMod M) • g := by
  revert M k ε g hg d hd
  exact @_root_.P2MW.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul.solution
