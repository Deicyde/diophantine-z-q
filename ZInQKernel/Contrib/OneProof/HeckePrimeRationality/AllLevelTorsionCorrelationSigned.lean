import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationModular

/-!
# Signed slopes for actual torsion correlations

Integer slopes are reduced by a proved nonnegative integer residue before
conversion to a natural index. The actual modular correction is retained
at its sharp canonical level, with the signed original row congruences.
-/

noncomputable section

open Complex Set Function Finset
open scoped Real UpperHalfPlane BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationSigned

open TorsionCorrelation TorsionCorrelationRows TorsionCorrelationModular DivisionSeriesMembership

/-- The actual correlation with a signed integer scalar on the torsion point. -/
def CInt (M : ℕ) (τ : ℍ) (n : ℕ) (s : ℤ) (A B : Point M) : ℂ :=
  ∑ T : DivisionIndex n,
    h M τ (A + divisionPoint M n T) * h M τ (B - s • divisionPoint M n T)

/-- Natural index of the integer residue; all reduction theorems guard n>0. -/
def residue (n : ℕ) (s : ℤ) : ℕ := (s % (n : ℤ)).toNat

/-- Nonnegativity and the strict upper bound are proved before conversion. -/
theorem integer_residue_bounds {n : ℕ} (hn : 0 < n) (s : ℤ) :
    0 ≤ s % (n : ℤ) ∧ s % (n : ℤ) < (n : ℤ) := by
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  exact ⟨Int.emod_nonneg s hnZ.ne', Int.emod_lt_of_pos s hnZ⟩

lemma residue_cast {n : ℕ} (hn : 0 < n) (s : ℤ) :
    ((residue n s : ℕ) : ℤ) = s % (n : ℤ) :=
  Int.toNat_of_nonneg (integer_residue_bounds hn s).1

lemma residue_lt {n : ℕ} (hn : 0 < n) (s : ℤ) : residue n s < n := by
  have hh := (integer_residue_bounds hn s).2
  rw [← residue_cast hn s] at hh
  exact_mod_cast hh

/-- The signed slope differs from its residue by a genuine integer multiple of n. -/
lemma residue_difference {n : ℕ} (hn : 0 < n) (s : ℤ) :
    (n : ℤ) ∣ s - ((residue n s : ℕ) : ℤ) := by
  rw [residue_cast hn s]
  refine ⟨s / (n : ℤ), ?_⟩
  have hh := Int.ediv_mul_add_emod s (n : ℤ)
  linear_combination -hh

/-- Signed scalar reduction on each actual killed torsion point. -/
theorem divisionPoint_signed_reduction {M n : ℕ} (hn : 0 < n) (hnM : n ∣ M)
    (s : ℤ) (T : DivisionIndex n) :
    s • divisionPoint M n T = (residue n s) • divisionPoint M n T := by
  let r : ℕ := residue n s
  obtain ⟨q, hq⟩ := residue_difference hn s
  have he : s = (r : ℤ) + (n : ℤ) * q := by
    change s - (r : ℤ) = (n : ℤ) * q at hq
    linear_combination hq
  calc
    s • divisionPoint M n T = ((r : ℤ) + (n : ℤ) * q) • divisionPoint M n T :=
      congrArg (fun a : ℤ => a • divisionPoint M n T) he
    _ = r • divisionPoint M n T := by
      rw [add_zsmul, mul_comm (n : ℤ) q, mul_zsmul]
      simp only [natCast_zsmul, divisionPoint_torsion hnM, zsmul_zero, add_zero]

/-- Actual signed C equals natural C at the guarded residue, including all zero classes. -/
theorem CInt_eq_C {M n : ℕ} (hn : 0 < n) (hnM : n ∣ M)
    (τ : ℍ) (s : ℤ) (A B : Point M) :
    CInt M τ n s A B = C M τ n (residue n s) A B := by
  unfold CInt C
  apply Finset.sum_congr rfl
  intro T _
  rw [divisionPoint_signed_reduction hn hnM s T]

/-- Matrix constraints in the original signed slope, entirely in integer arithmetic. -/
def ValidRowsInt (n : ℕ) (s : ℤ) (R : Rows) : Prop :=
  (R.det = (n : ℤ) ∨ R.det = -(n : ℤ)) ∧
    (n : ℤ) ∣ R.a - s * R.b ∧ (n : ℤ) ∣ R.c - s * R.d

/-- The natural-residue row constraints imply the original signed congruences. -/
theorem validRows_signed {n : ℕ} (hn : 0 < n) (s : ℤ) {R : Rows}
    (hv : ValidRows n (residue n s) R) : ValidRowsInt n s R := by
  have hd : (n : ℤ) ∣ ((residue n s : ℕ) : ℤ) - s := by
    simpa only [neg_sub] using (dvd_neg).mpr (residue_difference hn s)
  refine ⟨hv.1, ?_, ?_⟩
  · rw [show R.a - s * R.b =
      (R.a - ((residue n s : ℕ) : ℤ) * R.b) + (((residue n s : ℕ) : ℤ) - s) * R.b by ring]
    exact dvd_add hv.2.1 (dvd_mul_of_dvd_left hd _)
  · rw [show R.c - s * R.d =
      (R.c - ((residue n s : ℕ) : ℤ) * R.d) + (((residue n s : ℕ) : ℤ) - s) * R.d by ring]
    exact dvd_add hv.2.2 (dvd_mul_of_dvd_left hd _)

/-- All signed integer slopes have an actual single modular correction in
the independent series span and original-level integer-row products. -/
theorem signed_correlation_with_modular_correction (n : ℕ) (hn : 0 < n) (M : ℕ)
    (hM : 0 < M) (hnM : n ∣ M) (s : ℤ) (A B : Point M) :
    ∃ rows : List WeightedRow, ∃ E : WeightTwo (canonicalLevel n M),
      E ∈ divisionSpan (canonicalLevel n M) (canonicalLevel_pos n hM) ∧
      (∀ τ : ℍ, CInt M τ n s A B = rowSum M τ A B rows + E τ) ∧
      (∀ T ∈ rows, ValidRowsInt n s T.2) ∧
      (∀ T ∈ rows, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ)) := by
  obtain ⟨rows, E, hE, hvalue, hrows, hcoeff⟩ :=
    correlation_with_modular_correction n hn M hM hnM (residue n s) A B
  refine ⟨rows, E, hE, ?_, ?_, hcoeff⟩
  · intro τ
    rw [CInt_eq_C hn hnM]
    exact hvalue τ
  · intro T hT
    exact validRows_signed hn s (hrows T hT)

/-- Explicit all-integer correction value: exactly the canonical finite
sum of restricted actual defect forms for the nonnegative residue. -/
theorem signed_canonical_identity (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M)
    (hnM : n ∣ M) (s : ℤ) (A B : Point M) (τ : ℍ) :
    CInt M τ n s A B = rowSum M τ A B (rowTerms n hn (residue n s)) +
      canonicalCorrectionForm n hn M hM hnM (residue n s) A B τ := by
  rw [CInt_eq_C hn hnM, canonicalCorrectionForm_apply]
  exact (correlation_rows n hn M hM hnM τ (residue n s) A B).1

/-- The signed-slope statement at ambient nℓ and the exact sharp level n!ℓ. -/
theorem signed_correlation_paper_level (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ)
    (s : ℤ) (A B : Point (n * ℓ)) :
    ∃ rows : List WeightedRow, ∃ E : WeightTwo (n.factorial * ℓ),
      E ∈ divisionSpan (n.factorial * ℓ) (Nat.mul_pos (Nat.factorial_pos n) hℓ) ∧
      (∀ τ : ℍ, CInt (n * ℓ) τ n s A B = rowSum (n * ℓ) τ A B rows + E τ) ∧
      (∀ T ∈ rows, ValidRowsInt n s T.2) ∧
      (∀ T ∈ rows, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ)) := by
  obtain ⟨rows, E, hE, hvalue, hrows, hcoeff⟩ :=
    correlation_paper_level n ℓ hn hℓ (residue n s) A B
  refine ⟨rows, E, hE, ?_, ?_, hcoeff⟩
  · intro τ
    rw [CInt_eq_C hn (dvd_mul_right n ℓ)]
    exact hvalue τ
  · intro T hT
    exact validRows_signed hn s (hrows T hT)

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationSigned
