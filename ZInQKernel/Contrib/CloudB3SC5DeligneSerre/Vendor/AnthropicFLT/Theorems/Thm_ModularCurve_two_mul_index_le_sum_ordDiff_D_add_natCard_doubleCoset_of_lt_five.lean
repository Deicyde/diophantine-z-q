/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five (git blob 7114418326c6d8205384ef5089d9c7213629278c, sha256 17509c868d3787f665368032c7be55385154f5b5c6525ecc7597446c6d83fc68).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ < 5)
    (hℓM : ¬ ℓ ∣ M) (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    (S : Finset (AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS : ∀ Q, Q ∈ S ↔ 0 < Q.ord x) :
    2 * ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ) ≤
      ∑ Q ∈ S, Q.ordDiff (KaehlerDifferential.D K
          (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) x) +
        Nat.card (DoubleCoset.Quotient
          (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) +
        Nat.card (DoubleCoset.Quotient
          (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by
  revert M H ℓ hℓ hℓM K x hx S hS
  exact @_root_.P2MW.S_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five.solution
