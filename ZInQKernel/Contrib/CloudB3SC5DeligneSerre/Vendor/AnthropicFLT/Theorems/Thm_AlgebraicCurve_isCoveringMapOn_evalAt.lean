/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_isCoveringMapOn_evalAt (git blob 9ac5a3845950c6e6c16cf897abda1f651c66e2a1, sha256 aa04be0111aafec75f09e767d16c065fe36df981e0475895d9923893e58fec95).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isCoveringMapOn_evalAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.isCoveringMapOn_evalAt
    (F : Type*) [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (f : F) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({f} : Set F)) F] :
    ∃ B : Finset ℂ,
      IsCoveringMapOn
        (fun P : {P : Place ℂ F // f ∈ P.toValuationSubring} => Place.evalAt P.1 f)
        ((↑B : Set ℂ)ᶜ) ∧
      ∀ t : ℂ, t ∉ B →
        Nat.card {P : Place ℂ F // f ∈ P.toValuationSubring ∧ Place.evalAt P f = t} =
          Module.finrank (IntermediateField.adjoin ℂ ({f} : Set F)) F := by
  revert F hF f hf
  exact @_root_.P2MW.S_AlgebraicCurve_isCoveringMapOn_evalAt.solution
