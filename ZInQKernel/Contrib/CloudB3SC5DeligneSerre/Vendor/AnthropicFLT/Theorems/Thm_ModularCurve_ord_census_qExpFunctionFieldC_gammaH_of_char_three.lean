/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three (git blob 094619f3289eec2bf13e304b154c012e8db091b4, sha256 3ecd402244cab0191df0c10d9ef1c5dac7a5abcb3522a547eeed9f2034cfa79f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.ord_census_qExpFunctionFieldC_gammaH_of_char_three
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 3 ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 3]
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = jqModC K)
    (S : Finset (Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔ 0 < Q.ord x) :
    (∀ Q ∈ S, Q.ord x = 1 ∨ Q.ord x = 2 ∨ Q.ord x = 3 ∨ Q.ord x = 6) ∧
    (∑ Q ∈ S, Q.ord x = ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ)) ∧
    ((S.filter fun Q => Q.ord x = 1).card + 2 * (S.filter fun Q => Q.ord x = 2).card +
        (S.filter fun Q => Q.ord x = 3).card + 2 * (S.filter fun Q => Q.ord x = 6).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) ∧
    ((S.filter fun Q => Q.ord x = 1).card + (S.filter fun Q => Q.ord x = 2).card +
        2 * (S.filter fun Q => Q.ord x = 3).card + 3 * (S.filter fun Q => Q.ord x = 6).card =
      Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))) := by
  revert M H hM K x hx S hS
  exact @_root_.P2MW.S_ModularCurve_ord_census_qExpFunctionFieldC_gammaH_of_char_three.solution
