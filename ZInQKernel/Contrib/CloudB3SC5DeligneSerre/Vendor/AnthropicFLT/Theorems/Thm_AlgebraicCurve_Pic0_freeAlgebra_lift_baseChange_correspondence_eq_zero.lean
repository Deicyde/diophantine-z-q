/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero (git blob 5c77b702141fb7f42c64d5359be4e07b1ed5a12b, sha256 f18daf56c261c67b0d1b795a52f7ec8089a247c4935ca8463fbcb1eabc1c6e46).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : ι → Type*) [∀ i, Field (F'E i)] [∀ i, Algebra E (F'E i)] [∀ i, Algebra (F' i) (F'E i)]
    [∀ i, Algebra K (F'E i)] [∀ i, IsScalarTower K E (F'E i)] [∀ i, IsScalarTower K (F' i) (F'E i)]
    [∀ i, IsCurveOver E (F'E i)]
    (hfgE' : ∀ i, ∃ x' : F'E i, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set (F'E i))) (F'E i))
    (hgen' : ∀ i, IntermediateField.adjoin E (Set.range (algebraMap (F' i) (F'E i))) = ⊤)
    (φE ψE : ∀ i, FE →ₐ[E] F'E i)
    (hφcomm : ∀ i (f : F), φE i (algebraMap F FE f) = algebraMap (F' i) (F'E i) (φ i f))
    (hψcomm : ∀ i (f : F), ψE i (algebraMap F FE f) = algebraMap (F' i) (F'E i) (ψ i f))
    (hφE : ∀ i, (φE i).toRingHom.IsIntegral) (hψE : ∀ i, (ψE i).toRingHom.IsIntegral)
    (hFIE : ∀ i, FundamentalIdentityAlong E (φE i) (hφE i))
    (hfinE : ∀ i, FiniteAlong E (ψE i)) (hNE : ∀ i, NormFormulaAlong E (ψE i) (hfinE i)) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φE i) (ψE i) (hφE i) (hψE i) (hFIE i) (hfinE i) (hNE i)).toIntLinearMap)
        p = 0 := by
  revert K F hfg ι F' φ ψ hφ hψ hFI hfin hN p hp E FE hfgE hgen F'E hfgE' hgen' φE ψE hφcomm hψcomm hφE hψE hFIE hfinE hNE
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero.solution
