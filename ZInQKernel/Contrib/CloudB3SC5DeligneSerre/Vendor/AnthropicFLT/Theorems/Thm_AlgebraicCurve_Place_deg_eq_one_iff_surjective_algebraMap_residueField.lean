/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField (git blob 953d29750be59eadef04ba7c225a0eaf5eb0efed, sha256 be8eda0a64b229c3eebff8a45ffe87e18e7e719a071a0ece77f5a72fbee2fd7a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by
  revert K F v
  exact @_root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.solution
