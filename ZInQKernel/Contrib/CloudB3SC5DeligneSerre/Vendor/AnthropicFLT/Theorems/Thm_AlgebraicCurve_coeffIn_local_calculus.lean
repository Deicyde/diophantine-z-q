/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_coeffIn_local_calculus (git blob c1e3ec462b3e25a53139e2b65319a269dda095bd, sha256 9031b13cac425eb99d655b2d48700ffd28831191c95b3adb8ae5457b5d3db21d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_coeffIn_local_calculus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.coeffIn_local_calculus
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (Q : Place ℂ F) (hQ : Q ∈ ζ.source)
    (hζa : AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q))
    (hζd : deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q Q) ≠ 0)
    (θ : Ω[F⁄ℂ]) :
    (0 ≤ Q.ordDifferential θ →
      (∀ᶠ w in 𝓝 (ζ Q), coeffIn ζ θ w =
        Q.readDifferential θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) *
          deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ ζ.symm) w) ∧
      AnalyticAt ℂ (coeffIn ζ θ) (ζ Q) ∧
      ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
        coeffIn ζ θ ((ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
            deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y =
          Q.readDifferential θ y) ∧
    (-1 ≤ Q.ordDifferential θ →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G (ζ Q) ∧ ∀ᶠ w in 𝓝[≠] (ζ Q),
        coeffIn ζ θ w = Place.evalAt Q (Q.dCoordFn * Q.differentialCoeff θ) / (w - ζ Q) + G w) := by
  revert F hfg hF ζ Q hQ hζa hζd θ
  exact @_root_.P2MW.S_AlgebraicCurve_coeffIn_local_calculus.solution
