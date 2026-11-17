/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_dedekindPsi_pos (git blob f9c3dc37a665155317b7a7475caf53ca1ff21a0e, sha256 553848bba2be0f6cc94a1a57d78e60dfcd02e8db70889d908823b88fda9276d9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_le_dedekindPsi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_dedekindPsi_pos

open ModularCurve

theorem solution (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N :=
  lt_of_lt_of_le (Nat.pos_of_ne_zero hN) (ModularCurve.le_dedekindPsi N hN)
