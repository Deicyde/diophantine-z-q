/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex (git blob ec327b4e9448f196124d39d6b70aad51f1f19f3b, sha256 28c0fe43158b86bf9a2da6f14c102fb01eff99892ac15e3ebdd3dca12aa05869).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra ℂ (F' i)]
    [∀ i, HasPrincipalDivisors ℂ (F' i)]
    (φ ψ : ∀ i, F →ₐ[ℂ] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong ℂ (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong ℂ (ψ i)) (hN : ∀ i, NormFormulaAlong ℂ (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : ∀ ω ∈ regularDifferentials ℂ F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0 := by
  revert F hfg ι F' φ ψ hφ hψ hFI hfin hN p hp
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex.solution
