/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq (git blob 362623cc81366b40ba89a9c1c0878083dc6081c3, sha256 5c74d0e685cad26286ab49dc4c60d1660f493c950cbd3cc437a0335411540940).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂) (S : Finset ℕ)
    (ha : ∀ p : ℕ, p.Prime → p ∉ S → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → p ∉ S → ε₁ (p : ZMod M₁) = ε₂ (p : ZMod M₂)) :
    M₁ = M₂ ∧ ∀ n : ℕ, ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n := by
  revert M₁ M₂ k ε₁ ε₂ g₁ g₂ h₁ h₂ S ha hε
  exact @_root_.P2MW.S_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq.solution
