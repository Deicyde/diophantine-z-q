/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries (git blob 3cc14ca9fcafba1ca11de5a4d803cf8850109705, sha256 ff670c8362b7f149b9a6adcd269c204505c987432690acc2b1c280ff122dc651).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)
    (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order := by
  revert K F ι h
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.solution
