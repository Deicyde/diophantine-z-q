/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even (git blob 4a8935365760ef89693db012e0b95ac66241a13b, sha256 af355bb377411e143d60e631edf97fa3f4247512771097743df8cf6b285fa329).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := by
  revert N k hk
  exact @_root_.P2MW.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.solution
