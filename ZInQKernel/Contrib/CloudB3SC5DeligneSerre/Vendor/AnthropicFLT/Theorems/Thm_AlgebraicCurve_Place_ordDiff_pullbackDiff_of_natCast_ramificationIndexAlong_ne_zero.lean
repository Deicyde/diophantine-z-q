/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero (git blob e8e954cb4815b53b6a8128148471783c450a9054, sha256 d0b12353329b141462d095153a458d52e664d6986b4224ac35bcf4137a3aa27b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open KaehlerDifferential

theorem AlgebraicCurve.Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [PerfectField K]
    (x₀ : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (x : F') [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w' : Place K F') {ω : Ω[F⁄K]}
    (hω : ω ≠ 0)
    (he : ((Place.ramificationIndexAlong φ w' : ℕ) : K) ≠ 0) :
    w'.ordDiff (pullbackDiff φ ω)
      = (Place.ramificationIndexAlong φ w' : ℤ) * (w'.restrictAlong φ hφ).ordDiff ω
        + ((Place.ramificationIndexAlong φ w' : ℤ) - 1) := by
  revert K F F' x₀ x φ hφ w' ω hω he
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero.solution
