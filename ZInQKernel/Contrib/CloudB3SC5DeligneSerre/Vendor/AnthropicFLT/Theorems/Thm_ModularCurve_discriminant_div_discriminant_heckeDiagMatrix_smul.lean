/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul (git blob 81c3a6b993b623120babd0cdd973ecee8b6ead47, sha256 2640ce2fcfe7992b1562b14f0bd9cc2a801b5bf24d0d19c51efdaa49f571926d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) : ModularForm.discriminant (γ • τ) / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • γ • τ) = ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix N • τ) := by
  revert N γ hγ τ
  exact @_root_.P2MW.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul.solution
