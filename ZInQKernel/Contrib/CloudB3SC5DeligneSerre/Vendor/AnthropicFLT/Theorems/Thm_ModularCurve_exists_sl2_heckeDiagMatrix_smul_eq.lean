/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq (git blob 41bf281f82a459718d33acfe17f56ec0cec28431, sha256 6a1b83ae57af4aec5d430457808619148a7aee0b62c121c95b627b4787ee5d75).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ τ : UpperHalfPlane, ModularForm.heckeDiagMatrix N • γ • τ = γ' • ModularForm.heckeDiagMatrix N • τ) ∧ ∀ τ : UpperHalfPlane, UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ) (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) := by
  revert N γ hγ
  exact @_root_.P2MW.S_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.solution
