/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero (git blob e909471c136a8f5e29d88849f69764e7b554d4a9, sha256 28cf240444550f9c283f3fadd576e19282f41a9ac90a57aceffc46c3615617e2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PeriodPair.scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero (L : PeriodPair) (α : ℂˣ)
    (h₂ : (α : ℂ) ^ 4 = 1 ∨ L.g₂ = 0) (h₃ : (α : ℂ) ^ 6 = 1 ∨ L.g₃ = 0) :
    (L.scale α).lattice = L.lattice := by
  revert L α h₂ h₃
  exact @_root_.P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero.solution
