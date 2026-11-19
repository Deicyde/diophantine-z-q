/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice (git blob 81b3bbcf2264bee42a9e2479e6ca0a6bc27ef86e, sha256 b8cf4e1a0f1b6429f73b6ea4e01d419ce12d174e6764c286a9445199d92a9441).
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
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice
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
    {n : ℕ} (b : Fin n → ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (f : F) (Z : ℂ → Divisor ℂ F)
    (hZ : ∀ (t : ℂ) (v : Place ℂ F), Z t v = max (v.ord (f - algebraMap ℂ F t)) 0)
    (t₀ : ℂ) :
    ∀ᶠ t in 𝓝 t₀,
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ (Z t) -
          abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ (Z t₀) ∈
        pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by
  revert F hfg hF n b P₀ f Z hZ t₀
  exact @_root_.P2MW.S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice.solution
