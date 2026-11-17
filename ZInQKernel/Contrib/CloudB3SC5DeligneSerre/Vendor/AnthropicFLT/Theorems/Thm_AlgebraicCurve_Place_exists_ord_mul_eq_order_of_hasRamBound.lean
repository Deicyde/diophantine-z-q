/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound (git blob c02dc4d75a80923f1b599babdb3ad9431f57229c, sha256 47dbc0011ce0e502141c00e53361719acc55c51975cd6b7717141554ab15cd6f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_HahnSeries_RamificationBound
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound
    {K L F : Type*} [Field K] [Field L] [Algebra K L] [Field F] [Algebra K F]
    (φ : F →ₐ[K] HahnSeries ℚ L) {d : ℕ} (hd : 0 < d)
    (hφ : ∀ x : F, HahnSeries.HasRamBound d (φ x))
    (hnt : ∃ x : F, (φ x).order ≠ 0) :
    ∃ (w : AlgebraicCurve.Place K F) (g : ℚ), 0 < g ∧
      ∀ x : F, (w.ord x : ℚ) * g = (φ x).order := by
  revert K L F φ d hd hφ hnt
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound.solution
