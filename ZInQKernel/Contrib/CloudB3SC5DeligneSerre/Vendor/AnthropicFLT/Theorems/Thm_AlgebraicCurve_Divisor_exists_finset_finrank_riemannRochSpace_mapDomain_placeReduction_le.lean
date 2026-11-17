/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le (git blob c6ad6432b0e16c5bd665c3a1ce670994ece78f49, sha256 8763b552d6806bac7da7e79edbb186dbad2d7b0a80db5a7c1ae50b2d42cf148d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Divisor E FE) :
    ∃ S : Finset E, (0 : E) ∉ S ∧
      ∀ (A : ValuationSubring E) (r : Place E FE → Place K F),
        (∀ k : K, algebraMap K E k ∈ A) →
        (∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) →
        (∀ s ∈ S, A.valuation s = 1) →
        (∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
          ∃ a : E, a ∈ A ∧
            P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1) →
        Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) ≤
          Module.finrank E (riemannRochSpace D) := by
  revert K F E FE hfg hfgE hgen D
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le.solution
