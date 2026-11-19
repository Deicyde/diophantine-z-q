/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero (git blob 33cce66fe1e10d3fd6c6007e0ffd08c0ed103421, sha256 00062556d24f9749a4beb15f8593ccac68372d13769cfb70ac7a39b267d2d471).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {N p : ℕ} [NeZero N] (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 := by
  revert N p k hp hpN f hf
  exact @_root_.P2MW.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.solution
