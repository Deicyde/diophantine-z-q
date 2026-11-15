/-
Multiplication-etale construction: PushoutCotangent.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section
open scoped TensorProduct

namespace H101DirectGlobalDetection.SourceReuse

/-- The actual quotient square is a pushout; not a caller-supplied square. -/
theorem isPushout_quotient {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) : Algebra.IsPushout A (A ⧸ I) B (B ⧸ I.map (algebraMap A B)) := by
  refine Algebra.IsPushout.symm ⟨IsBaseChange.of_equiv (Ideal.quotMapEquivTensorQuot B).symm ?_⟩
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [LinearEquiv.symm_apply_eq]
  simp [Ideal.quotMapEquivTensorQuot, LinearEquiv.eq_symm_apply, Algebra.smul_def]

variable (A B A' B' κ : Type*) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing κ]
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A A' B B']
  [Algebra B' κ] [Algebra B κ] [IsScalarTower B B' κ]

/-- Genuine pushout cotangent equivalence after further extension of scalars. -/
def kaehlerTensorEquivOfIsPushout :
    κ ⊗[B] (KaehlerDifferential A B) ≃ₗ[κ] κ ⊗[B'] (KaehlerDifferential A' B') :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B B' κ κ
      (KaehlerDifferential A B)).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl κ κ)
      (KaehlerDifferential.tensorKaehlerEquiv A A' B B'))

/-- Its actual value on universal differentials; no desired commutative square is assumed. -/
theorem kaehlerTensorEquivOfIsPushout_tmul_D (b : B) :
    kaehlerTensorEquivOfIsPushout A B A' B' κ
        ((1 : κ) ⊗ₜ[B] KaehlerDifferential.D A B b) =
      (1 : κ) ⊗ₜ[B'] KaehlerDifferential.D A' B' (algebraMap B B' b) := by
  have hc : TensorProduct.AlgebraTensorModule.cancelBaseChange B B' κ κ
      (KaehlerDifferential A B) ((1 : κ) ⊗ₜ[B'] ((1 : B') ⊗ₜ[B]
        KaehlerDifferential.D A B b)) = (1 : κ) ⊗ₜ[B] KaehlerDifferential.D A B b := by
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp
  rw [kaehlerTensorEquivOfIsPushout, LinearEquiv.trans_apply, ← hc,
    LinearEquiv.symm_apply_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]

end H101DirectGlobalDetection.SourceReuse
