/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ordDiff_smul_of_perfectField (git blob 568425d74d622d95c30f9bc9cdf44bff3c5ecfe2, sha256 89ecbd5bee080efa8bfc677cb85974f8275c92cdf937127f9d26521d4729611b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_smul_of_perfectField

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
namespace Place
export _root_.AlgebraicCurve.Place (diffCoeff ordDiff ordDiff_def ord_uniformizer_alt uniformizer_alt ord ord_mul diffCoeff_smul_D_of_ord_eq_one diffCoeff_smul_D_eq_of_ord_eq_one exists_ord_eq_one)
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

private theorem H1_impl {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hrep : diffCoeff v.uniformizer_alt ω • KaehlerDifferential.D K F v.uniformizer_alt = ω :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht ω
  have hgo : g • ω = (g * diffCoeff v.uniformizer_alt ω) • KaehlerDifferential.D K F v.uniformizer_alt := by
    conv_lhs => rw [← hrep]
    rw [smul_smul]
  have hco : diffCoeff v.uniformizer_alt (g • ω) = g * diffCoeff v.uniformizer_alt ω := by
    rw [hgo]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hc0 : diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro h0
    apply hω
    rw [← hrep, h0, zero_smul]
  rw [ordDiff_def, ordDiff_def, hco, v.ord_mul hg hc0]

end AlgebraicCurve.Place

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω :=
  AlgebraicCurve.Place.H1_impl x v hg hω
