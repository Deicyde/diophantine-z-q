/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff (git blob c1dc9aa1ead543ef51f2775ff9a15d5318d37ab5, sha256 20ae49c5ef5c535f5acf479b6fa254c6100aa2fe71bd4a4a234901a9c56e286e).
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
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.exists_isUnit_det_evalAt_differentialCoeff
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    {n : ℕ} (b : Module.Basis (Fin n) K ↥(regularDifferentials K F)) :
    ∃ v : Fin n → Place K F, Function.Injective v ∧
      IsUnit (Matrix.det (Matrix.of fun i j : Fin n =>
        (v j).evalAt ((v j).differentialCoeff (b i : Ω[F⁄K])))) ∧
      ∀ f : F,
        (∀ w : Place K F, -((∑ j, Finsupp.single (v j) (1 : ℤ) : Divisor K F) w) ≤ w.ord f) →
          ∃ c : K, f = algebraMap K F c := by
  revert K F hfg n b
  exact @_root_.P2MW.S_AlgebraicCurve_exists_isUnit_det_evalAt_differentialCoeff.solution
