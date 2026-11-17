/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq (git blob ad58783bdd57d46ed14ff37d49b196c5f3d57181, sha256 3e4d992fc04ad2c214874e8488578d1bf57ef1c51d6998583d7a1b75ef77bb81).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups
theorem CuspForm.eq_zero_of_forall_vadd_inv_pow_eq
    {R q' : ℕ} [NeZero R] (hq' : 1 < q') (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ) :
    y = 0 := by
  revert R q' hq' k y h
  exact @_root_.P2MW.S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.solution
