/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex (git blob 4a1040f938ca084eace1c92f3e5b406c1171efcf, sha256 4ab8eeebe8af16e5d9424af4301860b07eeee30abecdea65e1bed6914d0941fa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] :
    ∃ (_ : TopologicalSpace (Place ℂ F)) (_ : ChartedSpace ℂ (Place ℂ F)),
      IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F) ∧ CompactSpace (Place ℂ F) ∧
      T2Space (Place ℂ F) ∧ ConnectedSpace (Place ℂ F) ∧
      ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
        MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
            (extChartAt 𝓘(ℂ, ℂ) v v) ∧
        meromorphicOrderAt
            (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
            (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ) := by
  revert F hfg
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex.solution
