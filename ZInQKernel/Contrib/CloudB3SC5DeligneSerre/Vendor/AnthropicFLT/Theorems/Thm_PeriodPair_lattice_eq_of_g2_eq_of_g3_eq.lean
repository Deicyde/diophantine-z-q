/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq (git blob 67b7c4b7eea62434ecca8ff173a660a32cc55636, sha256 fcf600a70514e22154d5511cb7e0987265c88499044863f74c5025a120ccfbe3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem PeriodPair.lattice_eq_of_g2_eq_of_g3_eq (L L' : PeriodPair)
    (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice := by
  revert L L' h₂ h₃
  exact @_root_.P2MW.S_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq.solution
