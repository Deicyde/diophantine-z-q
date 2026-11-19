/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_continuous_restrictAlong (git blob 626a63595cf54d19391a193b5b9b10f104533fca, sha256 7ebcedcc02ca6eac7a641f66865aa113158881ac33196b6c723ed193d5906d08).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_continuous_restrictAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
open scoped Manifold

theorem AlgebraicCurve.Place.continuous_restrictAlong
    (F F' : Type*) [Field F] [Algebra ℂ F] [Field F'] [Algebra ℂ F']
    [IsCurveOver ℂ F] [IsCurveOver ℂ F']
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [CompactSpace (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    [TopologicalSpace (Place ℂ F')] [ChartedSpace ℂ (Place ℂ F')] [T2Space (Place ℂ F')]
    (hF' : ∀ f : F', f ≠ 0 → ∀ w : Place ℂ F',
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) = (w.ord f : WithTop ℤ))
    (φ : F →ₐ[ℂ] F') (hφ : φ.toRingHom.IsIntegral) :
    Continuous fun w : Place ℂ F' => w.restrictAlong φ hφ := by
  revert F F' hF hF' φ hφ
  exact @_root_.P2MW.S_AlgebraicCurve_Place_continuous_restrictAlong.solution
