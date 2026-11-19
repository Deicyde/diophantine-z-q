/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange (git blob 7b0ea34462860750f4b0ad20f3ef26a30e7fb5ff, sha256 f3366bd2665661c65036a01e01c464f92ee3224ab2b5bda2c21fe064f6ac21db).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange {K E : Type*} [Field K] [Field E] [Algebra K E] (A B : IntermediateField K E) (φ : A →ₐ[K] B) : AlgebraicCurve.finrankAlong K φ = IntermediateField.relfinrank ((B.val.comp φ).fieldRange) B := by
  revert K E A B φ
  exact @_root_.P2MW.S_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange.solution
