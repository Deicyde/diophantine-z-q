/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction (git blob fd73a670324adba8b9dbc1dcfaefb7efce0d35eb, sha256 a535198c5a0438c525a9bcb64feb1e15234807c686dfe6f25e76edb0d9ee5d20).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction
    (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [IsAlgClosed E]
    [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)] [Algebra (RatFunc K) L]
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring (RatFunc E)) (ρ : O →+* L)
    (hO : ∀ c : E, algebraMap E (RatFunc E) c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ p : K[X],
      ∃ h : algebraMap E[X] (RatFunc E) (p.map (algebraMap K E)) ∈ O,
        ρ ⟨_, h⟩ = algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) p))
    (G : O) (N : RatFunc K) (hN : N ≠ 0) (hGN : ρ G = algebraMap (RatFunc K) L N)
    (S : Finset E) (hSA : ∀ β ∈ S, β ∉ A)
    (hS : ∀ β : E, β ∉ A → (placeOfPoint E β).ord (G : RatFunc E) ≠ 0 → β ∈ S) :
    (placeInfty K).ord N =
      (placeInfty E).ord (G : RatFunc E) + ∑ β ∈ S, (placeOfPoint E β).ord (G : RatFunc E) := by
  revert K E L A hKA hArat O ρ hO hker hρ G N hN hGN S hSA hS
  exact @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction.solution
