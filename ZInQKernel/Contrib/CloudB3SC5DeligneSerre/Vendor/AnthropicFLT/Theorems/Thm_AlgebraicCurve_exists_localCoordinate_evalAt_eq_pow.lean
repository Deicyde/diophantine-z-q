/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow (git blob 7e62be60723ac355f6a29e2bd9d0f0510fd0ecee, sha256 9b69b7f9f3b18e4ab53f25512a9523e0c366d498df8a0d85ee749906e4f26b23).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_localCoordinate_evalAt_eq_pow
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (v : Place ℂ F) (g : F) (hne : g ≠ 0) (hg : g ∈ v.toValuationSubring) (hg0 : v.evalAt g = 0) :
    ∃ (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (ρ : ℝ), 0 < ρ ∧
      v ∈ ζ.source ∧ ζ v = 0 ∧ ζ.target = Metric.ball 0 ρ ∧
      ζ.source ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source ∧
      AnalyticOnNhd ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) (extChartAt 𝓘(ℂ, ℂ) v '' ζ.source) ∧
      (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) v '' ζ.source, deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) v).symm) z ≠ 0) ∧
      ∀ P ∈ ζ.source, g ∈ P.toValuationSubring ∧ P.evalAt g = (ζ P) ^ (v.ord g).toNat := by
  revert F hF v g hne hg hg0
  exact @_root_.P2MW.S_AlgebraicCurve_exists_localCoordinate_evalAt_eq_pow.solution
