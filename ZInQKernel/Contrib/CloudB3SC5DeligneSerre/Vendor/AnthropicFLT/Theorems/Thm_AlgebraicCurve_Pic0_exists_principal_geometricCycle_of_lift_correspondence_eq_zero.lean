/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero (git blob d60cb4483b3930b3dd8c6c07a4f6a67413c2fb42, sha256 0c2f413364fdb6b30fee4ae6d803fcd7cc8d11526854b8bdb5dd602a851e6d4a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero
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
    (η : F →ₐ[K] E) :
    ∃ (g : FE) (_ : g ≠ 0) (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E)),
      (∀ P ∈ S, ∀ f : F,
        P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1) ∧
      (∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
        ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) ∧
      (∑ P ∈ S, Finsupp.single (y P) (P.ord g) : (F →ₐ[K] E) →₀ ℤ) =
        FreeAlgebra.lift ℤ (fun i => (Finsupp.liftAddHom fun e : F →ₐ[K] E =>
          zmultiplesHom ((F →ₐ[K] E) →₀ ℤ)
            (∑ᶠ σ ∈ {σ : F' i →ₐ[K] E | σ.comp (φ i) = e},
              Finsupp.single (σ.comp (ψ i)) (1 : ℤ))).toIntLinearMap) p (Finsupp.single η 1) := by
  revert K F hfg ι F' φ ψ hφ hψ hFI hfin hN p hp E FE hfgE hgen η
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_principal_geometricCycle_of_lift_correspondence_eq_zero.solution
