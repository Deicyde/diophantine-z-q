import ZInQKernel.Contrib.OneProof.RC.Eichler.Packing
import ZInQKernel.Contrib.OneProof.RC.Eichler.Stabilizer
import ZInQKernel.Contrib.OneProof.RC.AppF.Stage

/-! Field values for the existing Visibility and App F theta-stage records. Tex 8466–8468,
8605–8611 and 9067–9071. The field names in these records need no changes. -/

namespace ZInQ.Manuscript.RC.Eichler

variable {a b : ℚ} {R : Order a b}

theorem finite_classG (ha : a < 0) (hb : b < 0) (z : ClassSet R) :
    Finite (classG ha hb z) :=
  ((representative z).val.leftOrder ha hb).finite_G ha hb

/-- The automorphism weight of a class, in the type of `AppF.ThetaStage.w`. -/
noncomputable def classWeight (ha : a < 0) (hb : b < 0) (z : ClassSet R) : ℕ :=
  Nat.card (classG ha hb z)

theorem classWeight_pos (ha : a < 0) (hb : b < 0) (z : ClassSet R) :
    0 < classWeight ha hb z := by
  let := finite_classG ha hb z
  exact Nat.card_pos

theorem classWeight_dvd (ha : a < 0) (hb : b < 0) (z : ClassSet R) :
    classWeight ha hb z ∣ Odd.c0 :=
  class_card_G_dvd ha hb z

/-- The exact mass identity of `AppF.ThetaStage.adjoint`, from an equivalence
between the forward and reverse arrows and from counting arrows above each kernel.
Only the finite counting takes place here; identifying the kernels and reversal
with the ideal correspondence is a separate step. -/
theorem adjoint_of_arrow_equiv {X : Type*} {p : ℕ} [NeZero p]
    (nb : X → Option (ZMod p) → X) (G : X → Type*) (A : X → X → Type*)
    (fiber : ∀ i j, A i j ≃ {L : Option (ZMod p) // nb i L = j} × G j)
    (dual : ∀ i j, A i j ≃ A j i) (i j : X) :
    AppF.nbrCount nb i j * Nat.card (G j) = AppF.nbrCount nb j i * Nat.card (G i) := by
  classical
  have hc (i j : X) : Nat.card (A i j) = AppF.nbrCount nb i j * Nat.card (G j) := by
    rw [Nat.card_congr (fiber i j), Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_subtype, AppF.nbrCount]
  rw [← hc, ← hc, Nat.card_congr (dual i j)]

end ZInQ.Manuscript.RC.Eichler

/-! Axiom audit -/

#print axioms ZInQ.Manuscript.RC.Eichler.finite_classG
#print axioms ZInQ.Manuscript.RC.Eichler.classWeight
#print axioms ZInQ.Manuscript.RC.Eichler.classWeight_pos
#print axioms ZInQ.Manuscript.RC.Eichler.classWeight_dvd
#print axioms ZInQ.Manuscript.RC.Eichler.adjoint_of_arrow_equiv
