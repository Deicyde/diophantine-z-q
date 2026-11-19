/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring (git blob add6ef17dc1e64e7d7454513188b3d7ef9adbfe2, sha256 3959c27973cba84b7a2985cf8ab792b60cd962401447635f4ace6ee60bb66d89).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] (A : ValuationSubring K) {j : F}
    (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {B : Subring F} (hconst : ∀ a : A, algebraMap K F a ∈ B) (hjB : j ∈ B)
    (hint : ∀ b : B,
      IsIntegral (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {j})) (b : F))
    (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮)
    (a₀ : A) (hja : (⟨j, hjB⟩ : B) - ⟨algebraMap K F a₀, hconst a₀⟩ ∈ 𝔮) :
    ∃ w : AlgebraicCurve.Place K F,
      0 < w.ord (j - algebraMap K F a₀) ∧
      ∀ b : B, b ∈ 𝔮 ↔ ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
        ((b : F) - algebraMap K F a) ∈ w.toValuationSubring.nonunits := by
  revert K F A j hj B hconst hjB hint 𝔮 h𝔮A a₀ hja
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.solution
