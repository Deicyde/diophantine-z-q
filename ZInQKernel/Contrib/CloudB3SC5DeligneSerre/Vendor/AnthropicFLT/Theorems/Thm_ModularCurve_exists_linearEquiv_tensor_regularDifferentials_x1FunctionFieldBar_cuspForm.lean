/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm (git blob 62edeaf2fdbf75018124a8a743ab9ca2b754ef5a, sha256 1a02d0d9727f193f401ab72684162d470661f5eca97836764276f035ece8a6c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped TensorProduct

theorem ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[AlgebraicClosure ℚ]
          ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
              ↥(ModularCurve.x1FunctionFieldBar M)) ≃ₗ[ℂ]
        CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ∀ ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
          ↥(ModularCurve.x1FunctionFieldBar M)),
        ModularCurve.coeffMap ι₀
            (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
              (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(e (1 ⊗ₜ ω))) := by
  revert M ι₀
  exact @_root_.P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.solution
