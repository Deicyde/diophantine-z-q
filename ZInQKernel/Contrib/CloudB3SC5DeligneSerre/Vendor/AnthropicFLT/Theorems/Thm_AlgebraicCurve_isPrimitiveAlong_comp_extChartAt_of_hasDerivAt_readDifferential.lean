/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential (git blob 59b287412b77c2f372535e92002125ac1f50c226, sha256 a43d8211cd8e6285576e347b4dc2a1c8d58a84e0fe6ee648ca1b72d723d1a6d0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (η : Ω[F⁄ℂ]) (v : Place ℂ F) (U : Set (Place ℂ F)) (hU : IsOpen U)
    (hUv : U ⊆ (extChartAt 𝓘(ℂ, ℂ) v).source)
    (hηU : ∀ u ∈ U, 0 ≤ u.ordDifferential η)
    (hcoeff : ∀ u ∈ U, v.differentialCoeff η ∈ u.toValuationSubring)
    (hunif : ∀ u ∈ U, v.dCoordFn ∈ u.toValuationSubring)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ u ∈ U, HasDerivAt Φ (v.readDifferential η (extChartAt 𝓘(ℂ, ℂ) v u))
      (extChartAt 𝓘(ℂ, ℂ) v u))
    {P Q : Place ℂ F} (γ : Path P Q) (hγ : ∀ t, γ t ∈ U) :
    IsPrimitiveAlong η γ (fun t => Φ (extChartAt 𝓘(ℂ, ℂ) v (γ t))) := by
  revert F hfg hF η v U hU hUv hηU hcoeff hunif Φ hΦ P Q γ hγ
  exact @_root_.P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential.solution
