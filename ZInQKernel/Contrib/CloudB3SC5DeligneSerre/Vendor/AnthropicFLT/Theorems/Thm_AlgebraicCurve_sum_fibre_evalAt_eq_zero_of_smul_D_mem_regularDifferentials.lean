/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials (git blob e1bd5a106e125233e2d79d670a53566d3fa53c7b, sha256 01e8dbb640b902fc46b3f0908f72fd4d04ef263a21ca77f689d2c01dbe698f01).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials
    (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (f h : F) (hω : h • KaehlerDifferential.D K F f ∈ regularDifferentials K F)
    (t : K)
    (hsimple : ∀ v : Place K F,
      0 < v.ord (f - algebraMap K F t) → v.ord (f - algebraMap K F t) = 1)
    (Z : Finset (Place K F)) (hZ : ∀ v : Place K F, v ∈ Z ↔ 0 < v.ord (f - algebraMap K F t)) :
    ∑ v ∈ Z, v.evalAt h = 0 := by
  revert K F hfg f h hω t hsimple Z hZ
  exact @_root_.P2MW.S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials.solution
