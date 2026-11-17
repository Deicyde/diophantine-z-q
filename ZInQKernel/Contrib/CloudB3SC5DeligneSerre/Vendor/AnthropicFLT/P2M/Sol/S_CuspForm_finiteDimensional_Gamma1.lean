/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_finiteDimensional_Gamma1 (git blob bf9b644cced43413121aefe6d37e70e175157e5f, sha256 31e0a15cfbbc1b01cae58f330a5bd78e99f9b0667089d7329783d0028220acac).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_finiteDimensional_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_finiteDimensional_Gamma1

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M : ℕ) [NeZero M] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) k) := by
  haveI := ModularForm.finiteDimensional_of_isArithmetic
    (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k
  exact FiniteDimensional.of_injective
    (CuspForm.toModularFormₗ : CuspForm (CongruenceSubgroup.Gamma1 M) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma1 M) k)
    CuspForm.toModularFormₗ_injective
