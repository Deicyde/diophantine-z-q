import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Models
import ZInQKernel.Contrib.OneProof.RC.Odd.ThetaLocal

/-! The (p ∣ m) weight (tex 8536–8549). The explicit orbit representatives
for the nonzero nilpotents are provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix _root_.ZInQ.Manuscript.RC.Odd

section Residue
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Intertwiner for the nonzero nilpotent orbit. -/
def NilBasis (A : Mat F) (g : GL (Fin 2) F) : Prop :=
  A * (g : Mat F) = (g : Mat F) * X0

/-- All nonzero trace-zero, determinant-zero matrices have a nilpotent basis. -/
theorem nilBasis_exists (A : Mat F) (ht : A.trace = 0) (hd : A.det = 0) (hn : A ≠ 0) :
    ∃ g : GL (Fin 2) F, NilBasis A g := by
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  have h11 : A 1 1 = -A 0 0 := by linear_combination ht
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · exfalso
      apply hn
      have h0 : A 0 0 * A 0 0 = 0 := by
        rw [h11, hb, zero_mul, sub_zero, mul_neg, neg_eq_zero] at hd
        exact hd
      have hh : A 0 0 = 0 := (mul_eq_zero.mp h0).elim id id
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hh, hb, hc, h11]
    · let G : Mat F := !![A 0 0, 1; A 1 0, 0]
      have hG : G.det ≠ 0 := by simp [G, Matrix.det_fin_two_of, hc]
      refine ⟨GeneralLinearGroup.mkOfDetNeZero G hG, ?_⟩
      change A * G = G * X0
      have hh : A 0 0 = 0 := by
        have h0 : A 0 0 * A 0 0 = 0 := by
          simpa only [h11, hb, zero_mul, sub_zero, mul_neg, neg_eq_zero] using hd
        exact (mul_eq_zero.mp h0).elim id id
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [G, X0, Matrix.mul_apply, Fin.sum_univ_two, h11, hb, hh]
  · let G : Mat F := !![A 0 1, 0; A 1 1, 1]
    have hG : G.det ≠ 0 := by simp [G, Matrix.det_fin_two_of, hb]
    refine ⟨GeneralLinearGroup.mkOfDetNeZero G hG, ?_⟩
    change A * G = G * X0
    rw [h11] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [G, X0, Matrix.mul_apply, Fin.sum_univ_two, h11]
    · ring
    · linear_combination -hd

theorem nilBasis_sign_eq {A : Mat F} {g h : GL (Fin 2) F}
    (hg : NilBasis A g) (hh : NilBasis A h) :
    quadraticChar F (g : Mat F).det = quadraticChar F (h : Mat F).det := by
  apply quadraticChar_det_eq_of_conj
  change ((↑h⁻¹ : Mat F) * (g : Mat F)) * X0 =
    X0 * ((↑h⁻¹ : Mat F) * (g : Mat F))
  unfold NilBasis at hg hh
  have hy : X0 * (↑h⁻¹ : Mat F) = (↑h⁻¹ : Mat F) * A := by
    calc
      X0 * (↑h⁻¹ : Mat F) =
          (↑h⁻¹ : Mat F) * ((h : Mat F) * X0) * (↑h⁻¹ : Mat F) := by
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      _ = (↑h⁻¹ : Mat F) * A := by
        rw [← hh, Matrix.mul_assoc, Matrix.mul_assoc A, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_assoc, ← hg, ← Matrix.mul_assoc, ← hy, Matrix.mul_assoc]

/-- The sign on the nonzero nilpotent orbit, extended by zero. -/
noncomputable def nilSign (A : Mat F) : ℤ :=
  open Classical in
  if h : ∃ g, NilBasis A g then quadraticChar F (h.choose : Mat F).det else 0

theorem nilSign_of_basis {A : Mat F} {g : GL (Fin 2) F} (hg : NilBasis A g) :
    nilSign A = quadraticChar F (g : Mat F).det := by
  have h : ∃ g, NilBasis A g := ⟨g, hg⟩
  rw [nilSign, dite_eq_left h]
  exact nilBasis_sign_eq h.choose_spec hg

theorem nilSign_conj (u : GL (Fin 2) F) (A : Mat F) :
    nilSign ((↑u⁻¹ : Mat F) * A * (u : Mat F)) =
      quadraticChar F (u : Mat F).det * nilSign A := by
  have step (v : GL (Fin 2) F) (B : Mat F) (g : GL (Fin 2) F) (hg : NilBasis B g) :
      NilBasis ((v : Mat F) * B * (↑v⁻¹ : Mat F)) (v * g) := by
    unfold NilBasis at *
    simp only [Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (↑v⁻¹ : Mat F),
      Units.inv_mul, Matrix.one_mul, hg]
  by_cases h : ∃ g, NilBasis A g
  · obtain ⟨g, hg⟩ := h
    have hg' : NilBasis ((↑u⁻¹ : Mat F) * A * (u : Mat F)) (u⁻¹ * g) := by
      simpa only [inv_inv] using step u⁻¹ A g hg
    rw [nilSign_of_basis hg, nilSign_of_basis hg', Units.val_mul,
      Matrix.det_mul, map_mul]
    have ht : quadraticChar F (↑u⁻¹ : Mat F).det = quadraticChar F (u : Mat F).det := by
      have hprod : quadraticChar F (↑u⁻¹ : Mat F).det * quadraticChar F (u : Mat F).det = 1 := by
        rw [← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one]
      rcases quadraticChar_dichotomy (Matrix.isUnits_det_units u).ne_zero with h | h <;>
        rw [h] at hprod ⊢ <;> omega
    rw [ht]
  · have h' : ¬ ∃ g, NilBasis ((↑u⁻¹ : Mat F) * A * (u : Mat F)) g := by
      rintro ⟨g, hg⟩
      have hb := step u _ g hg
      have he : (u : Mat F) * ((↑u⁻¹ : Mat F) * A * (u : Mat F)) * (↑u⁻¹ : Mat F) =
          A := by
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
          ← Matrix.mul_assoc (u : Mat F) (↑u⁻¹ : Mat F) A, Matrix.one_mul]
      rw [he] at hb
      exact h ⟨u * g, hb⟩
    rw [nilSign, dite_eq_right h', nilSign, dite_eq_right h, mul_zero]

theorem nilSign_scale (v : Fˣ) (A : Mat F) :
    nilSign ((v : F) • A) = quadraticChar F (v : F) * nilSign A := by
  let D (w : Fˣ) : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero
    !![(w : F), 0; 0, 1] (by simp [Matrix.det_fin_two_of])
  have step (w : Fˣ) (B : Mat F) (g : GL (Fin 2) F) (hg : NilBasis B g) :
      NilBasis ((w : F) • B) (g * D w) := by
    unfold NilBasis at *
    change ((w : F) • B) * ((g : Mat F) * (D w : Mat F)) =
      ((g : Mat F) * (D w : Mat F)) * X0
    rw [smul_mul_assoc, ← Matrix.mul_assoc, hg, Matrix.mul_assoc, ← mul_smul_comm,
      ← mul_smul_comm, Matrix.mul_assoc]
    rw [mul_smul_comm, ← smul_mul_assoc]
    exact congrArg (fun z : Mat F => (g : Mat F) * z) (diag_conj_X0 (w : F)).symm
  by_cases h : ∃ g, NilBasis A g
  · obtain ⟨g, hg⟩ := h
    rw [nilSign_of_basis hg, nilSign_of_basis (step v A g hg), Units.val_mul, Matrix.det_mul,
      map_mul, mul_comm]
    simp [D, Matrix.det_fin_two_of]
  · have h' : ¬ ∃ g, NilBasis ((v : F) • A) g := by
      rintro ⟨g, hg⟩
      have hh := step v⁻¹ _ g hg
      rw [smul_smul, Units.inv_mul, one_smul] at hh
      exact h ⟨g * D v⁻¹, hh⟩
    rw [nilSign, dite_eq_right h', nilSign, dite_eq_right h, mul_zero]

end Residue

variable (p : ℕ) [Fact p.Prime]

/-- Exactly (v_p(det x)=1), tested without assigning a valuation to zero. -/
def NilSupport (x : TraceZero ℤ_[p]) : Prop :=
  (p : ℤ_[p]) ∣ x.val.det ∧ ¬ (p : ℤ_[p]) ^ 2 ∣ x.val.det

/-- The nilpotent weight on the integral trace-zero model. -/
noncomputable def nilWeight {O : Type*} [Ring O] (x : TraceZero ℤ_[p]) : O :=
  open Classical in
  if NilSupport p x then
    (nilSign (x.val.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)) : O)
  else 0

/-- On the support reduction is nonzero and has trace and determinant zero. -/
theorem nilSupport_reduction (x : TraceZero ℤ_[p]) (hx : NilSupport p x) :
    let A := x.val.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
    A.trace = 0 ∧ A.det = 0 ∧ A ≠ 0 := by
  have hker (a : ℤ_[p]) : PadicInt.toZMod a = 0 ↔ (p : ℤ_[p]) ∣ a := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.trace_fin_two]
    simp only [Matrix.map_apply, ← map_add]
    rw [← Matrix.trace_fin_two, x.property, map_zero]
  · simp only [Matrix.det_fin_two, Matrix.map_apply, ← map_mul, ← map_sub]
    exact (hker _).mpr (by simpa only [Matrix.det_fin_two] using hx.1)
  · intro h
    have he (i j : Fin 2) : (p : ℤ_[p]) ∣ x.val i j :=
      (hker _).mp (congrFun (congrFun h i) j)
    exact hx.2 (by
      rw [Matrix.det_fin_two, pow_two]
      exact dvd_sub (mul_dvd_mul (he 0 0) (he 1 1)) (mul_dvd_mul (he 0 1) (he 1 0)))

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights in
#print axioms nilBasis_exists
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms nilBasis_sign_eq
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms nilSign_of_basis
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms nilSign_conj
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms nilSign_scale
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms nilSupport_reduction
