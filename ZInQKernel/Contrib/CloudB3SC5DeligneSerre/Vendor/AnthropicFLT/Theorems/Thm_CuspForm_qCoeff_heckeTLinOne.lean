/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_qCoeff_heckeTLinOne (git blob 56c8ace9002023cbbdfcdf5fa8c29032d54f1f10, sha256 6fbd524aaf53b6da40eddf5b7157accf2324729d6e88f9aec478ac2a8a59a7bf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_Gamma1HeckeOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_qCoeff_heckeTLinOne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem CuspForm.qCoeff_heckeTLinOne {M : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLinOne k hp hpM f) n =
      ModularFormClass.qCoeff f (p * n) +
        (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff (CuspForm.diamondLinOne M k p f) (n / p) else 0) := by
  revert M k p hp hpM f n
  exact @_root_.P2MW.S_CuspForm_qCoeff_heckeTLinOne.solution
