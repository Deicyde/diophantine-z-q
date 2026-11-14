import NativeEndTrace
import C10AbVarPointAction

set_option autoImplicit false

/-!
# Proposed canonical same-field Frobenius trace application

SOURCE-ONLY APPLICATION, NOT YET COMPILED OR KERNEL-CHECKED TOGETHER.
Both imports must be validated against the same exact canonical Objects source.
The existing rational trace supplier is reused unchanged. No integer-polynomial,
global GQ, reduction, descent or C10-square conclusion is asserted.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace C10Frobenius.NativeTracePairing

variable {k : Type} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)

/-- Proposed direct application to the same original q-power Frobenius endomorphism. -/
theorem exists_common_arithmetic_trace (A : PkgI3.AbVar k)
    (C : Type) [Field C] [CharZero C] :
    ∃ c : C, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] (j : C →+* L),
      LinearMap.trace L (TensorProduct ℚ_[ℓ] L (A.V ℓ))
        ((A.galRep ℓ (NativePointAction.arithmeticGal p f hcard)).baseChange L) = j c := by
  obtain ⟨c, hc⟩ := AxiomBridge.NativeEndTrace.exists_common_coefficient_trace A
    (NativeFiniteField.endomorphism p f hcard A) C
  refine ⟨c, ?_⟩
  intro ℓ _ hℓ L _ _ _ j
  rw [← NativePointAction.homT_baseChange_eq_galRep p f hcard A ℓ]
  exact hc ℓ hℓ L j

end C10Frobenius.NativeTracePairing
