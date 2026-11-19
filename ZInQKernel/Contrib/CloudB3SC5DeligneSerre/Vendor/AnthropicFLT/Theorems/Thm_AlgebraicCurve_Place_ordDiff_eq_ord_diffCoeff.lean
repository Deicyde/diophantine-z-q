/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff (git blob cd317459364ca6386f1eb47b28f5392f15d6cd70, sha256 6a5fa792200cca9161b88c194ae52f3c183838481d8a920b7bc506113db3f32a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ord (AlgebraicCurve.Place.diffCoeff t ω) := by
  revert K F x v t ht ω
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ordDiff_eq_ord_diffCoeff.solution
