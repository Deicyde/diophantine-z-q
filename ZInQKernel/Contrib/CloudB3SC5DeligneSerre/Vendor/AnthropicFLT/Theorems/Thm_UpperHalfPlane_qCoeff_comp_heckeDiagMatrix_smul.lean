/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul (git blob 4d39d57808aa894edf4639656f2041a9a79f58dd, sha256 de79376373324028b8ef4ba9aaa96650f9348d194caf0ca58f88e54e0cab3196).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 := by
  revert f hper hhol hbdd d hd n
  exact @_root_.P2MW.S_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.solution
