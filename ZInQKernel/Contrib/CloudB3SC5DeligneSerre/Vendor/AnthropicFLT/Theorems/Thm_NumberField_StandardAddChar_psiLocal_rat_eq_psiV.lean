/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV (git blob 8a3a6cb2c0ea95bf01c234d52a16e2c65493fbf0, sha256 d1b120680d99bff07b81fe3acb891ac2e6226f72a1e5706355bc4781c091654c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain

theorem NumberField.StandardAddChar.psiLocal_rat_eq_psiV
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    psiLocal ℚ v = psiV v := by
  revert v
  exact @_root_.P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiV.solution
