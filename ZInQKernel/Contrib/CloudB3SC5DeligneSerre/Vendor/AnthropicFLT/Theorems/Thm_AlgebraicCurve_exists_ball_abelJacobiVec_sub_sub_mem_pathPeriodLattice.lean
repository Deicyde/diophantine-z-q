/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice (git blob 0f9f69e62cb933ef6b4f84dcc2f0f2f81a2f41f1, sha256 78ebaf18ac42b10448fac99c3eed3c4f3e00766ea3122efb1ea06454536d8123).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ P : Place ℂ F) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r ⊆ (extChartAt 𝓘(ℂ, ℂ) P).target ∧
      ∃ Φ : Fin n → ℂ → ℂ,
        (∀ i, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          HasDerivAt (Φ i) (P.readDifferential (b i) z) z) ∧
        ∀ z ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) P P) r,
          abelJacobiVec b P₀ ((extChartAt 𝓘(ℂ, ℂ) P).symm z) - abelJacobiVec b P₀ P -
              (fun i => Φ i z - Φ i (extChartAt 𝓘(ℂ, ℂ) P P)) ∈ pathPeriodLattice b := by
  revert F hfg hF n b hb P₀ P
  exact @_root_.P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.solution
