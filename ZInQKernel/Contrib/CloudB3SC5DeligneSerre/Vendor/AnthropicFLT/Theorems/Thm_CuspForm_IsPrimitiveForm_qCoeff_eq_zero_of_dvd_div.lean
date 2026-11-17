/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div (git blob cbbbeb0ef100024350bc57bfcbcf92eb535bfc3e, sha256 3dd02e33c9c0972973e3aa69e94287d1714952a1511f824490c6b622a8017cc6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div
    (M : ℕ) [NeZero M] (k : ℤ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hqq : q ∣ M / q)
    (ε' : DirichletCharacter ℂ (M / q)) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hqM) ε') g) :
    ModularFormClass.qCoeff g q = 0 := by
  revert M k q hq hqM hqq ε' g hg
  exact @_root_.P2MW.S_CuspForm_IsPrimitiveForm_qCoeff_eq_zero_of_dvd_div.solution
