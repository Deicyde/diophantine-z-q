/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff (git blob c16929ac28feea46844dec8b49841fcc001660f1, sha256 7484b3b3c1fed976075c2164b128e07b46ad57289389070f0771a0fc0be14353).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.eq_ord_of_addHom_of_nonneg_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (φ : F → ℤ) (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y) (hone : ∃ t, t ≠ 0 ∧ φ t = 1) (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring)) {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  revert K F w φ hmul hone hiff x hx
  exact @_root_.P2MW.S_AlgebraicCurve_Place_eq_ord_of_addHom_of_nonneg_iff.solution
