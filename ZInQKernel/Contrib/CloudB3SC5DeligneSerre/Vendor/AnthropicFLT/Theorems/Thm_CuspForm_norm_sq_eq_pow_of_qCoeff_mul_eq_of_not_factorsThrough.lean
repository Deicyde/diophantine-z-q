/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough (git blob 5d3529279284daeca70f4afa909ffa7e3857e9b9, sha256 4b52c182eee52f3d6f927b93c0857feec0d4dfd583f0140919eb5d2d2de30848).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M)
    (hε : ¬ ε.FactorsThrough (M / ℓ)) (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0)
    (hg : CuspForm.HasNebentypus ε g) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (ℓ * n) = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 = (ℓ : ℝ) ^ (k - 1) := by
  revert M k ε ℓ hℓ hℓM hε g hg0 hg a ha
  exact @_root_.P2MW.S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.solution
