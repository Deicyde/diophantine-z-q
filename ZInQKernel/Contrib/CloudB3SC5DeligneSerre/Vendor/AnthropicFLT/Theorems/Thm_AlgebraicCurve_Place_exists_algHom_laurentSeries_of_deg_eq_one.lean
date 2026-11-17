/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one (git blob 28b047d076161f539e04730f553d2b9254648696, sha256 31902b51f7c073bb76aabec58921a59f58d1a92db9bbf9427cca2247e9614a65).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1)
    (t : F) (ht : w.ord t = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ t = HahnSeries.single (1 : ℤ) (1 : K) ∧ ∀ x : F, (φ x).order = w.ord x := by
  revert K F w hw t ht
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.solution
