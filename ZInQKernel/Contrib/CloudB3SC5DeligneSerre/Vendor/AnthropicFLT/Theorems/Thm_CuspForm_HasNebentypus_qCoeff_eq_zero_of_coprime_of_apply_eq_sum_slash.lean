/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash (git blob 88fbb0297012eefd964ac9e0fbaf4abd2012ebdd, sha256 6c9b02ea23b793e93f972044af150c9124057f50ba821d2169852c00980310f1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash
    {q t : ℕ} (hq : q ≠ 0) (hqt : q ∣ t) {k : ℤ} (ε : DirichletCharacter ℂ t)
    (E : CuspForm (CongruenceSubgroup.Gamma1 (q * t)) k)
    (hE : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_mul_left t q) ε) E)
    {K : ℕ} (hK : K ≠ 0) (hKq : Nat.Coprime K q)
    (hzero : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff E n = 0)
    {N' : ℕ} (Φ : CuspForm (CongruenceSubgroup.Gamma1 N') k)
    (hΦ : ∀ τ : UpperHalfPlane, Φ τ = ∑ j ∈ Finset.range q,
        ((⇑E : UpperHalfPlane → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ)
    (n : ℕ) (hn : Nat.Coprime n K) : ModularFormClass.qCoeff Φ n = 0 := by
  revert q t hq hqt k ε E hE K hK hKq hzero N' Φ hΦ n hn
  exact @_root_.P2MW.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash.solution
