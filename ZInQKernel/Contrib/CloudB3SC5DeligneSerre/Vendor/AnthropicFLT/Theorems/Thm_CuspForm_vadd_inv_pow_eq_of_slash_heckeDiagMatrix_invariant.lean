/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant (git blob 491c8dff0330af3a447b17a0c228fdef47671a95, sha256 641f7beabbe6f7a75674f6830694a125923af9f5e59023f650360488b1e5c948).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups
theorem CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q')
    (j : ℕ) (τ : ℍ) :
    y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ := by
  revert R q' hq' hq'R k y hy j τ
  exact @_root_.P2MW.S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.solution
