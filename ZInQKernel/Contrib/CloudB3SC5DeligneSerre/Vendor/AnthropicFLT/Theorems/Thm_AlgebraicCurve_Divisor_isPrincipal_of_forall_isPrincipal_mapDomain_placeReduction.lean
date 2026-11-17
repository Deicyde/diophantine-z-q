/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction (git blob 3587b2075b664cd5d14e41a58cab513de3e88df6, sha256 90d6369e20a71c5e2056dff540952c4e05cc351d84fd0d25f6c00ba456be70cc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Divisor.isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) (hD : D.degree = 0)
    (h : ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
      (∀ k : K, algebraMap K E k ∈ A) →
      (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
      (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
        ∃ a : E, a ∈ A ∧
          P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
      Divisor.IsPrincipal (K := K) (F := F) (Finsupp.mapDomain r D)) :
    D.IsPrincipal := by
  revert K F E FE hfg hfgE hgen D hD h
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_forall_isPrincipal_mapDomain_placeReduction.solution
