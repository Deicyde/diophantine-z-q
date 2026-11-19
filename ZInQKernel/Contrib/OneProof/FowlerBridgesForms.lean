import ZInQKernel.Contrib.OneProof.FowlerBridges

/-!
# The scope of the remaining Cox forms dictionary

These definitions specify the cardinality part of Cox (1989), Theorem 7.7. They do not enter
`FowlerProp27Print` or its application, which use proper fractional ideal classes.
-/

namespace HDec.CMBranch.FowlerBridges

open NumberField Module TauCeti.GlobalNumberFields

/-- A primitive positive definite integral binary quadratic form of discriminant `Δ`. -/
structure PrimitivePositiveForm (Δ : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  leading_pos : 0 < a
  discr_eq : b ^ 2 - 4 * a * c = Δ
  discr_neg : Δ < 0
  primitive : Int.gcd (Int.gcd a b) c = 1

/-- Evaluate `ax² + bxy + cy²` on an integral vector. -/
def PrimitivePositiveForm.eval {Δ : ℤ} (Q : PrimitivePositiveForm Δ) (v : Fin 2 → ℤ) : ℤ :=
  Q.a * v 0 ^ 2 + Q.b * v 0 * v 1 + Q.c * v 1 ^ 2

/-- The completed square formula for the quadratic form. -/
theorem PrimitivePositiveForm.four_mul_eval {Δ : ℤ} (Q : PrimitivePositiveForm Δ)
    (v : Fin 2 → ℤ) :
    4 * Q.a * Q.eval v = (2 * Q.a * v 0 + Q.b * v 1) ^ 2 - Δ * v 1 ^ 2 := by
  rw [PrimitivePositiveForm.eval]
  linear_combination -(v 1 ^ 2) * Q.discr_eq

/-- The form takes strictly positive values on nonzero integral vectors. -/
theorem PrimitivePositiveForm.eval_pos {Δ : ℤ} (Q : PrimitivePositiveForm Δ)
    {v : Fin 2 → ℤ} (hv : v ≠ 0) : 0 < Q.eval v := by
  have hp : 0 < 4 * Q.a * Q.eval v := by
    rw [Q.four_mul_eval]
    by_cases h : v 1 = 0
    · rw [h]
      have hx : v 0 ≠ 0 := by
        intro hx
        apply hv
        funext i
        fin_cases i <;> assumption
      have hh : 2 * Q.a * v 0 ≠ 0 := mul_ne_zero
        (mul_ne_zero (by decide) Q.leading_pos.ne') hx
      simpa using (sq_pos_of_ne_zero hh)
    · exact sub_pos.mpr ((mul_neg_of_neg_of_pos Q.discr_neg (sq_pos_of_ne_zero h)).trans_le
        (sq_nonneg _))
  exact pos_of_mul_pos_right hp (by have := Q.leading_pos; positivity)

/-- Proper equivalence is change of variables by `SL₂(ℤ)`. The orbit relation on functions
is pulled back along evaluation. Its orientation is immaterial since matrices are invertible. -/
def properFormSetoid (Δ : ℤ) : Setoid (PrimitivePositiveForm Δ) :=
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) ((Fin 2 → ℤ) → ℤ) := arrowAction
  Setoid.comap PrimitivePositiveForm.eval
    (MulAction.orbitRel (Matrix.SpecialLinearGroup (Fin 2) ℤ) ((Fin 2 → ℤ) → ℤ))

/-- An explicit description of the equivalence relation used in the form quotient. -/
theorem properFormSetoid_iff {Δ : ℤ} (P Q : PrimitivePositiveForm Δ) :
    (properFormSetoid Δ).r P Q ↔
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ v, P.eval v = Q.eval (M • v) := by
  let : MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ) ((Fin 2 → ℤ) → ℤ) := arrowAction
  change P.eval ∈ MulAction.orbit (Matrix.SpecialLinearGroup (Fin 2) ℤ) Q.eval ↔ _
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨M, h⟩
    exact ⟨M⁻¹, fun v => (congrFun h v).symm⟩
  · rintro ⟨M, h⟩
    refine ⟨M⁻¹, funext fun v => ?_⟩
    change Q.eval ((M⁻¹)⁻¹ • v) = P.eval v
    simpa only [inv_inv] using (h v).symm

/-- The proper classes of primitive positive definite integral forms of discriminant `Δ`. -/
abbrev ProperFormClasses (Δ : ℤ) := Quotient (properFormSetoid Δ)

/-- Smallest remaining cardinality statement from Cox (1989), Theorem 7.7:
the proper ideal class number equals the number of proper form classes of the same discriminant.
The equivalence formulation also establishes finiteness of the form classes.
This is a scoped goal, not an input to the Fowler row. -/
def CoxFormClassEquivalence : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [IsTotallyComplex k], finrank ℚ k = 2 →
    ∀ O : NumberFieldOrder k, Nonempty (ProperIdealClasses O ≃ ProperFormClasses O.discr)

/-- Once the forms dictionary is proved, it can be composed with the ideal-class dictionary. -/
theorem card_pic_eq_card_properFormClasses_of (hCox : CoxFormClassEquivalence)
    {k : Type} [Field k] [NumberField k] (R : Subring k) (hR : IsImagQuadOrder k R) :
    Nat.card (CommRing.Pic R) = Nat.card (ProperFormClasses (orderDisc R)) := by
  let : IsTotallyComplex k := hR.1
  let O := toOrder R hR
  obtain ⟨e⟩ := hCox k hR.2.1 O
  obtain ⟨b⟩ := exists_intBasis_of_isImagQuadOrder R hR
  have hd : O.discr = orderDisc R := (O.discr_eq_discr b).symm.trans (orderDisc_eq_discr R hR b).symm
  calc
    Nat.card (CommRing.Pic R) = properClassNumber O := card_pic_eq_properClassNumber R hR
    _ = Nat.card (ProperFormClasses O.discr) := Nat.card_congr e
    _ = Nat.card (ProperFormClasses (orderDisc R)) := by rw [hd]

end HDec.CMBranch.FowlerBridges
