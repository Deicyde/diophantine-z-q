/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension (git blob f06df9d54b14373a8b9b03834cb8e9a3c3e72f06, sha256 54e7dd97c50adf573001c3dc5ef9108637f2c042de48410b9c1943b06de9a649).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

universe u v w x

theorem AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type w) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E : Type x) (FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    ∃ (F'E : Type (max w x)) (_ : Field F'E) (_ : Algebra E F'E) (_ : Algebra F' F'E)
      (_ : Algebra K F'E) (_ : IsScalarTower K E F'E) (_ : IsScalarTower K F' F'E)
      (_ : IsCurveOver E F'E)
      (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
      (_ : FundamentalIdentityAlong E φE hφE) (hfinE : FiniteAlong E ψE)
      (_ : NormFormulaAlong E ψE hfinE),
      (∃ x' : F'E, Transcendental E x' ∧
        FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E) ∧
      IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤ ∧
      (∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f)) ∧
      (∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f)) ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ (Q : Place E FE) (e' : F →ₐ[K] E),
        (∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) →
          Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q =
            (∑ᶠ σ ∈ {σ : F' →ₐ[K] E | σ.comp φ = e},
              Finsupp.single (σ.comp ψ) (1 : ℤ) : (F →ₐ[K] E) →₀ ℤ) e') ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ e' : F →ₐ[K] E, ∀ f : F,
            Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) ∧
      (∀ P : Place E FE, (∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring) := by
  revert K F hfg F' φ ψ hφ hψ hFI hfin hN E FE hfgE hgen
  exact @_root_.P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.solution
