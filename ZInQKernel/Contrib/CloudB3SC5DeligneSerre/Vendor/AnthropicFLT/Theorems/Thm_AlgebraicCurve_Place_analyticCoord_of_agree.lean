/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_analyticCoord_of_agree (git blob fe1786f3e44daa113cf3c5f13b1341b3d24ba18e, sha256 4eff6d84f3535534d56a309204f4c22b2553210e8fa1067f2973f3a640a51557).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_analyticCoord_of_agree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff
open AlgebraicCurve

theorem AlgebraicCurve.Place.analyticCoord_of_agree {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f)
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hread : ∀ Q ∈ ζ.source, ζ Q = Place.evalAt Q f)
    (P : Place ℂ F) (hP : P ∈ ζ.source)
    (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
  revert F hF hrat f hf ζ hread P hP hfP hord
  exact @_root_.P2MW.S_AlgebraicCurve_Place_analyticCoord_of_agree.solution
