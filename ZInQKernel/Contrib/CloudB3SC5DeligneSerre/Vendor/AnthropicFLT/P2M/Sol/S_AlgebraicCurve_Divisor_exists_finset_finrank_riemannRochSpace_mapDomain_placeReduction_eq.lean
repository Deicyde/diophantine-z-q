/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq (git blob 863de3da62cd652928e2cdf18e343e0614634c7c, sha256 71ae6dd196ea1ea006607e24105d03fcdbbb151e962ce096a6935578ccfebdf9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_eq

open AlgebraicCurve

theorem solution
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
        Module.finrank K (riemannRochSpace (Finsupp.mapDomain r D)) =
          Module.finrank E (riemannRochSpace D) := by
  obtain ⟨S, hS0, hle⟩ :=
    AlgebraicCurve.Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le
      K F E FE hfg hfgE hgen D
  refine ⟨S, hS0, fun A r hKA hArat hS hr => le_antisymm (hle A r hKA hArat hS hr) ?_⟩
  exact
    AlgebraicCurve.Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction
      K F E FE hfg hfgE hgen D A r hKA hArat hr
