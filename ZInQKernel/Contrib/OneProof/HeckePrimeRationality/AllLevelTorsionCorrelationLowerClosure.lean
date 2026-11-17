import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationLowerProducts
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinLowerTraceClosure

/-!
# Lower-series and admissible-product closure of signed correlations

The already constructed canonical correction is genuinely invariant at the
lower level. The proved arbitrary invariant-series descent supplies a
lower series correction by the actual normalized trace. Its value then
recovers the exact correlation identity and actual product-span membership.
This is a torsion-correlation result, not general principal-product trace closure.
-/

noncomputable section

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationLowerClosure

open TorsionCorrelation TorsionCorrelationEnlarge TorsionCorrelationRows
open TorsionCorrelationModular TorsionCorrelationSigned TorsionCorrelationLower
open TorsionCorrelationLowerProducts DivisionSeriesMembership

/-- An actual lower-series correction, constructed by normalized trace of
the explicit canonical upper defect form, not by subtracting row values. -/
def descendedErrorForm (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ) (A B : Point ℓ) : WeightTwo ℓ :=
  DivisionEisensteinLevelMaps.normalizedTrace ℓ (canonicalLevel n (n * ℓ))
    (canonicalLevel_pos n (Nat.mul_pos hn hℓ)) (upperErrorForm ℓ n hℓ hn s A B)

/-- Arbitrary verified series-span trace closure supplies actual lower-span membership. -/
theorem descendedErrorForm_mem_seriesSpan (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) :
    descendedErrorForm ℓ n hℓ hn s A B ∈ DivisionEisensteinLevelMaps.seriesSpan ℓ hℓ :=
  DivisionEisensteinLowerClosure.trace_seriesSpan_all hℓ
    (canonicalLevel_pos n (Nat.mul_pos hn hℓ)) (lower_level_dvd_canonical ℓ n)
    (upperErrorForm_mem_seriesSpan ℓ n hℓ hn s A B)

/-- The invariant canonical upper correction is recovered by actual restriction of its lower trace. -/
theorem descendedErrorForm_restriction (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) :
    DivisionEisensteinLevelMaps.restriction ℓ (canonicalLevel n (n * ℓ)) (lower_level_dvd_canonical ℓ n)
      (descendedErrorForm ℓ n hℓ hn s A B) = upperErrorForm ℓ n hℓ hn s A B :=
  DivisionEisensteinLevelMaps.restriction_normalizedTrace_of_invariant hℓ
    (canonicalLevel_pos n (Nat.mul_pos hn hℓ)) (lower_level_dvd_canonical ℓ n)
    (upperErrorForm ℓ n hℓ hn s A B) (upperErrorForm_invariant ℓ n hℓ hn s A B)

/-- The constructed lower correction has exactly the explicit finite canonical-error value. -/
theorem descendedErrorForm_apply (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) (τ : ℍ) :
    descendedErrorForm ℓ n hℓ hn s A B τ = upperErrorForm ℓ n hℓ hn s A B τ := by
  have hh := congrArg (fun F : WeightTwo (canonicalLevel n (n * ℓ)) => F τ)
    (descendedErrorForm_restriction ℓ n hℓ hn s A B)
  exact hh

/-- The lower trace equals the genuine lower modular difference by actual evaluation. -/
theorem descendedErrorForm_eq_lowerErrorForm (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) : descendedErrorForm ℓ n hℓ hn s A B = lowerErrorForm ℓ n hℓ hn s A B := by
  apply _root_.ModularForm.ext
  intro τ
  rw [descendedErrorForm_apply, lowerErrorForm_apply]

/-- Membership in the pair-indexed independent series span uses the proved generator-range bridge. -/
theorem descendedErrorForm_mem_divisionSpan (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) : descendedErrorForm ℓ n hℓ hn s A B ∈ divisionSpan ℓ hℓ := by
  rw [← seriesSpan_eq_divisionSpan ℓ hℓ]
  exact descendedErrorForm_mem_seriesSpan ℓ n hℓ hn s A B

/-- Actual equality of lower modular forms with original-level constrained row products. -/
theorem lowerCorrelationForm_decomposition (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) :
    lowerCorrelationForm ℓ n hℓ hn s A B =
      rowSumForm ℓ hℓ A B (rowTerms n hn (residue n s)) + descendedErrorForm ℓ n hℓ hn s A B := by
  rw [descendedErrorForm_eq_lowerErrorForm, lowerErrorForm]
  abel

/-- The lower signed correlation belongs to the actual admissible degree-two product span. -/
theorem lowerCorrelationForm_mem_productSpan (ℓ n : ℕ) (hℓ : 0 < ℓ) (h3 : 3 ≤ ℓ)
    (hn : 0 < n) (s : ℤ) (A B : Point ℓ) :
    lowerCorrelationForm ℓ n hℓ hn s A B ∈ TorsionQuadraticGenerators.productSpan ℓ hℓ := by
  rw [lowerCorrelationForm_decomposition]
  exact (TorsionQuadraticGenerators.productSpan ℓ hℓ).add_mem
    (rowSumForm_mem_productSpan ℓ hℓ A B _)
    (divisionSpan_le_productSpan ℓ hℓ h3 (descendedErrorForm_mem_divisionSpan ℓ n hℓ hn s A B))

/-- A concrete actual lower-level correlation form with no invariance, series
membership, or product-spanning premise among the caller's hypotheses. -/
theorem actual_lower_correlation_in_productSpan (ℓ n : ℕ) (h3 : 3 ≤ ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) :
    ∃ F : WeightTwo ℓ, F ∈ TorsionQuadraticGenerators.productSpan ℓ (by omega) ∧
      ∀ τ : ℍ, F τ = CInt (n * ℓ) τ n s (levelMap n ℓ (by omega) A) (levelMap n ℓ (by omega) B) := by
  have hℓ : 0 < ℓ := by omega
  exact ⟨lowerCorrelationForm ℓ n hℓ hn s A B,
    lowerCorrelationForm_mem_productSpan ℓ n hℓ h3 hn s A B,
    lowerCorrelationForm_apply ℓ n hℓ hn s A B⟩

/-- The exact signed correlation at the original lower level, modulo a
constructed genuine lower independent-series correction. -/
theorem lower_correlation_rows_and_series_error (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n)
    (s : ℤ) (A B : Point ℓ) :
    ∃ rows : List WeightedRow, ∃ E : WeightTwo ℓ,
      E ∈ divisionSpan ℓ hℓ ∧
      (∀ τ : ℍ, CInt (n * ℓ) τ n s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B) =
        rowSum ℓ τ A B rows + E τ) ∧
      (∀ T ∈ rows, ValidRowsInt n s T.2) ∧
      (∀ T ∈ rows, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ)) := by
  refine ⟨rowTerms n hn (residue n s), descendedErrorForm ℓ n hℓ hn s A B,
    descendedErrorForm_mem_divisionSpan ℓ n hℓ hn s A B, ?_, ?_, rowTerms_coeff n hn (residue n s)⟩
  · intro τ
    have hh := congrArg (fun F : WeightTwo ℓ => F τ) (lowerCorrelationForm_decomposition ℓ n hℓ hn s A B)
    rw [lowerCorrelationForm_apply, add_apply, rowSumForm_apply] at hh
    exact hh
  · intro T hT
    exact validRows_signed hn s (rowTerms_valid n hn (residue n s) T hT)

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationLowerClosure
