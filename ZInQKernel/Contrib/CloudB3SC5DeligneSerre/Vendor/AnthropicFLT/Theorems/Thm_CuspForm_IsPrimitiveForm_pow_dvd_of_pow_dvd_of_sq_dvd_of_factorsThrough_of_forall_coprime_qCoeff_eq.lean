/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq (git blob 1bc734924f48b2b675f3569da692f36825179d93, sha256 21958a8281d2e8cdb08224efcf1fedf3a54ef8dbe806a9d63d067ea9b3cb4b9e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
    {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℤ}
    {ε₁ : DirichletCharacter ℂ M₁} {ε₂ : DirichletCharacter ℂ M₂}
    {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 M₂) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ →
      ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n M₂ → ε₁ (n : ZMod M₁) = ε₂ (n : ZMod M₂))
    {q : ℕ} (hq : q.Prime) (hqM : q ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / q))
    (j : ℕ) (hj : q ^ j ∣ M₁) : q ^ j ∣ M₂ := by
  revert M₁ M₂ k ε₁ ε₂ g₁ g₂ h₁ h₂ ha hε q hq hqM hε₁ j hj
  exact @_root_.P2MW.S_CuspForm_IsPrimitiveForm_pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq.solution
