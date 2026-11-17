import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDivisionSeriesMembership
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelation

/-!
# Actual raw correlation corrections in the independent series span

The common weight-one scale is nonzero. Dividing the actual quadratic form
by its square gives exactly the quadratic defect of the zero-extended raw
function on ambient residue classes. Finite correction sums stay in the
same ambient-level series span. Correlation recurrences retain positivity,
ambient divisibility and the given preimage relation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Complex ModularForm
open scoped Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionSeriesCorrelation

open ZInQ.Contrib.HeckePrimeRationality
open DivisionSeriesMembership

/-- The actual scale square is nonzero; no normalization divisor is assumed invertible. -/
theorem scale_sq_ne_zero : TorsionWeierstrassData.scale ^ 2 ≠ (0 : _root_.Complex) :=
  pow_ne_zero 2 TorsionWeierstrassData.scale_ne_zero

/-- The actual scaled defect equals the square of the common scale times the raw defect. -/
theorem quadraticDefect_eq_scale_sq_D (M : _root_.Nat) (hM : 0 < M)
    (a b c d : _root_.Int) (τ : _root_.UpperHalfPlane) :
    TorsionQuadraticCases.quadraticDefect M a b c d τ = TorsionWeierstrassData.scale ^ 2 *
      TorsionCorrelation.D M τ (TorsionCorrelation.label M a b) (TorsionCorrelation.label M c d) := by
  rw [TorsionCorrelation.D, TorsionCorrelation.label_add,
    TorsionCorrelation.h_label hM τ a b, TorsionCorrelation.h_label hM τ c d,
    TorsionCorrelation.h_label hM τ (a + c) (b + d)]
  unfold TorsionQuadraticCases.quadraticDefect TorsionWeierstrassData.lambdaValue
  ring

/-- The actual raw defect as a genuine modular form at its ambient level. -/
def normalizedDefectForm (M : _root_.Nat) (hM : 0 < M)
    (P Q : TorsionCorrelation.Point M) : WeightTwo M :=
  (TorsionWeierstrassData.scale ^ 2)⁻¹ • quadraticDefectForm M hM
    (P.1.val : ℤ) (P.2.val : ℤ) (Q.1.val : ℤ) (Q.2.val : ℤ)

/-- Literal equality with the frozen raw defect on canonical ambient labels, including all bad cases. -/
theorem normalizedDefectForm_apply (M : _root_.Nat) (hM : 0 < M)
    (P Q : TorsionCorrelation.Point M) (τ : _root_.UpperHalfPlane) :
    normalizedDefectForm M hM P Q τ = TorsionCorrelation.D M τ P Q := by
  change (TorsionWeierstrassData.scale ^ 2)⁻¹ *
    quadraticDefectForm M hM (P.1.val : ℤ) (P.2.val : ℤ) (Q.1.val : ℤ) (Q.2.val : ℤ) τ = _
  rw [quadraticDefectForm_apply, quadraticDefect_eq_scale_sq_D M hM,
    TorsionCorrelation.label_val hM P, TorsionCorrelation.label_val hM Q]
  exact inv_mul_cancel_left₀ scale_sq_ne_zero _

/-- The normalized actual raw defect belongs to the independent series span at its ambient level. -/
theorem normalizedDefectForm_mem_divisionSpan (M : _root_.Nat) (hM : 0 < M)
    (P Q : TorsionCorrelation.Point M) : normalizedDefectForm M hM P Q ∈ divisionSpan M hM :=
  (divisionSpan M hM).smul_mem _ (quadraticDefectForm_mem_divisionSpan M hM
    (P.1.val : ℤ) (P.2.val : ℤ) (Q.1.val : ℤ) (Q.2.val : ℤ))

/-- The degenerate raw first-zero case remains a negative square. -/
theorem normalizedDefectForm_zero_left_apply (M : _root_.Nat) (hM : 0 < M)
    (Q : TorsionCorrelation.Point M) (τ : _root_.UpperHalfPlane) :
    normalizedDefectForm M hM 0 Q τ = -(TorsionCorrelation.h M τ Q) ^ 2 := by
  rw [normalizedDefectForm_apply]
  exact TorsionCorrelation.D_zero_left hM τ Q

/-- The degenerate raw second-zero case remains a negative square. -/
theorem normalizedDefectForm_zero_right_apply (M : _root_.Nat) (hM : 0 < M)
    (P : TorsionCorrelation.Point M) (τ : _root_.UpperHalfPlane) :
    normalizedDefectForm M hM P 0 τ = -(TorsionCorrelation.h M τ P) ^ 2 := by
  rw [normalizedDefectForm_apply]
  exact TorsionCorrelation.D_zero_right hM τ P

/-- Opposite raw classes retain their actual negative-square defect. -/
theorem normalizedDefectForm_neg_apply (M : _root_.Nat) (hM : 0 < M)
    (P : TorsionCorrelation.Point M) (τ : _root_.UpperHalfPlane) :
    normalizedDefectForm M hM P (-P) τ = -(TorsionCorrelation.h M τ P) ^ 2 := by
  rw [normalizedDefectForm_apply]
  exact TorsionCorrelation.D_neg hM τ P

/-- The explicit finite sum of ambient quadratic corrections as a genuine modular form. -/
def defectSumForm (M : _root_.Nat) (hM : 0 < M) (n s : _root_.Nat)
    (A B' : TorsionCorrelation.Point M) : WeightTwo M :=
  ∑ T : TorsionCorrelation.DivisionIndex n, ∑ U : TorsionCorrelation.DivisionIndex s,
    normalizedDefectForm M hM (A + TorsionCorrelation.divisionPoint M n T)
      (B' - TorsionCorrelation.divisionPoint M n T + TorsionCorrelation.divisionPoint M s U)

theorem defectSumForm_apply (M : _root_.Nat) (hM : 0 < M) (n s : _root_.Nat)
    (A B' : TorsionCorrelation.Point M) (τ : _root_.UpperHalfPlane) :
    defectSumForm M hM n s A B' τ = TorsionCorrelation.defectSum M τ n s A B' := by
  simp only [defectSumForm, _root_.sum_apply, normalizedDefectForm_apply, TorsionCorrelation.defectSum]

/-- Finite correction sums remain in the same ambient-level span, with no descent or trace claim. -/
theorem defectSumForm_mem_divisionSpan (M : _root_.Nat) (hM : 0 < M) (n s : _root_.Nat)
    (A B' : TorsionCorrelation.Point M) : defectSumForm M hM n s A B' ∈ divisionSpan M hM := by
  apply (divisionSpan M hM).sum_mem
  intro T _
  apply (divisionSpan M hM).sum_mem
  intro U _
  exact normalizedDefectForm_mem_divisionSpan M hM _ _

/-- The normalized finite correction in the actual correlation recurrence. -/
def correlationCorrectionForm (M : _root_.Nat) (hM : 0 < M) (n s : _root_.Nat)
    (A B' : TorsionCorrelation.Point M) : WeightTwo M :=
  (1 / (s : ℂ)) • defectSumForm M hM n s A B'

theorem correlationCorrectionForm_apply (M : _root_.Nat) (hM : 0 < M) (n s : _root_.Nat)
    (A B' : TorsionCorrelation.Point M) (τ : _root_.UpperHalfPlane) :
    correlationCorrectionForm M hM n s A B' τ =
      (1 / (s : ℂ)) * TorsionCorrelation.defectSum M τ n s A B' := by
  change (1 / (s : ℂ)) * defectSumForm M hM n s A B' τ = _
  rw [defectSumForm_apply]

theorem correlationCorrectionForm_mem_divisionSpan (M : _root_.Nat) (hM : 0 < M) (n s : _root_.Nat)
    (A B' : TorsionCorrelation.Point M) : correlationCorrectionForm M hM n s A B' ∈ divisionSpan M hM :=
  (divisionSpan M hM).smul_mem _ (defectSumForm_mem_divisionSpan M hM n s A B')

/-- The frozen exact correlation recurrence with its independently series-valued correction.
The two torsion orders divide the ambient level, and the actual preimage relation is retained. -/
theorem correlation_recurrence_with_series_correction {M n s : _root_.Nat}
    (hM : 0 < M) (hn : 0 < n) (hs : 0 < s) (hnM : n ∣ M) (hsM : s ∣ M)
    (τ : _root_.UpperHalfPlane) (A B B' : TorsionCorrelation.Point M) (hB : s • B' = B) :
    TorsionCorrelation.C M τ n s A B =
      (n : ℂ) * TorsionCorrelation.h M τ (n • A) * TorsionCorrelation.h M τ (s • A + B) -
      ((n : ℂ) / (s : ℂ)) * TorsionCorrelation.C M τ s n (A + B') (-(n • B')) +
      correlationCorrectionForm M hM n s A B' τ := by
  rw [correlationCorrectionForm_apply]
  exact TorsionCorrelation.correlation_recurrence hM hn hs hnM hsM τ A B B' hB

end ZInQ.Contrib.HeckePrimeRationality.DivisionSeriesCorrelation
