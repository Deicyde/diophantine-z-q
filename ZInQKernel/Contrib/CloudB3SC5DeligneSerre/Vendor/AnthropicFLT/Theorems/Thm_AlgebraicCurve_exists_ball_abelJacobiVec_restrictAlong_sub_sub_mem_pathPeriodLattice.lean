/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice (git blob ef57baac4e75b39899fdc513c453cf422807fa55, sha256 7ccb54f34d26989ba949f6f8ceea48ea25cf3bb2e1e855ae54fca1bf07f1091f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve hiding exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (F' : Type*) [Field F'] [Algebra ℂ F']
    (hfg' : ∃ y : F', Transcendental ℂ y ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({y} : Set F')) F')
    [IsCurveOver ℂ F']
    [TopologicalSpace (Place ℂ F')] [ChartedSpace ℂ (Place ℂ F')] [T2Space (Place ℂ F')]
    (hF' : ∀ f : F', f ≠ 0 → ∀ w : Place ℂ F',
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) = (w.ord f : WithTop ℤ))
    (ψ : F →ₐ[ℂ] F') (hψ : ψ.toRingHom.IsIntegral)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ : Place ℂ F) (W : Place ℂ F') :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r ⊆ (extChartAt 𝓘(ℂ, ℂ) W).target ∧
      ∃ Ψ : Fin n → ℂ → ℂ,
        (∀ i, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r,
          HasDerivAt (Ψ i) (W.readDifferential (Differential.pullbackAlong ψ (b i)) u) u) ∧
        ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r,
          abelJacobiVec b P₀ (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong ψ hψ) -
              abelJacobiVec b P₀ (W.restrictAlong ψ hψ) -
              (fun i => Ψ i u - Ψ i (extChartAt 𝓘(ℂ, ℂ) W W)) ∈ pathPeriodLattice b := by
  revert F hfg hF F' hfg' hF' ψ hψ n b hb P₀ W
  exact @_root_.P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice.solution
