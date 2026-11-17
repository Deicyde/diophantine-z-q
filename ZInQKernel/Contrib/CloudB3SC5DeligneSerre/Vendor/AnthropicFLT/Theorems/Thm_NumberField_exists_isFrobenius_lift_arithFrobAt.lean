/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_exists_isFrobenius_lift_arithFrobAt (git blob 0d4e2fbec8fd694fae4cf246e9f1d2423b4973c2, sha256 3377527fefdbd4180b387f747c7ee8ba57fa13fc38f01af5c22a6fe608ca1481).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Normal.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_exists_isFrobenius_lift_arithFrobAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped NumberField Pointwise
theorem NumberField.exists_isFrobenius_lift_arithFrobAt
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)]
    [Finite (𝓞 E ⧸ Q)] :
    ∃ (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) (_ : Qt.IsMaximal)
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Qt.LiesOver Q ∧ AlgEquiv.restrictNormal τ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q ∧
      (∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) ∧
      ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt := by
  revert E ℓ hℓ Q
  exact @_root_.P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt.solution
