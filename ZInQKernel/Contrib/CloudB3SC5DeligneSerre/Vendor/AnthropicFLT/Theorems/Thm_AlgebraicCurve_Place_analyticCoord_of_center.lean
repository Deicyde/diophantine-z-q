/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_analyticCoord_of_center (git blob fd0e40d1bc8950716e129f2c7c670038c0476fa2, sha256 5d1d6014ec49ff3100948d3b19847ae1de57b1574bd67122fc1785a0402a8e3b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_analyticCoord_of_center

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff
open AlgebraicCurve

theorem AlgebraicCurve.Place.analyticCoord_of_center {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] {v : Place ℂ F}
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hsub : ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (han : AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm)
      (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source))
    (hder : ∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source,
      deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0)
    (P : Place ℂ F) (hP : P ∈ ζ.source) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
  revert F v ζ hsub han hder P hP
  exact @_root_.P2MW.S_AlgebraicCurve_Place_analyticCoord_of_center.solution
