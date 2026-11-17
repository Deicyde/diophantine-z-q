/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_pathIntegral_finset_sum_smul (git blob 5e1caba9ede374be944b257ed3e7f21ed3befd99, sha256 55b33319a3feb925bf6d1813d5718a5f7fd71aed7c65d599eae8574316efc36a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_pathIntegral_finset_sum_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.pathIntegral_finset_sum_smul
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (ι : Type) (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ := by
  revert F hF ι s c θ P P' γ hreg hprim
  exact @_root_.P2MW.S_AlgebraicCurve_pathIntegral_finset_sum_smul.solution
