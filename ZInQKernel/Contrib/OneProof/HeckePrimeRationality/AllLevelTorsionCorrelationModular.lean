import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationRows
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelDivisionSeriesCorrelation
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinLevelMaps

/-!
# Canonical-level modular corrections for actual torsion correlations

The correction is a finite sum of actual defect modular forms, restricted
upward from their positive levels. Its membership is in the independent
convergent division-series span, not a claimed whole Eisenstein space.
-/

noncomputable section

open Complex Set Function
open scoped Real UpperHalfPlane BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationModular

open TorsionCorrelation TorsionCorrelationRows DivisionSeriesMembership

/-- Every two-coordinate integer vector is its explicit pair of entries. -/
lemma vector_eq_pair (a : Fin 2 → ℤ) : a = ![a 0, a 1] := by
  funext i
  fin_cases i <;> rfl

/-- The vector-indexed and pair-indexed series generators have the same range. -/
theorem series_generator_ranges_eq (N : ℕ) (hN : 0 < N) :
    Set.range (EisensteinWeightTwo.divisionEisensteinMF N hN) =
      Set.range (fun p : ℤ × ℤ => EisensteinWeightTwo.divisionEisensteinMF N hN ![p.1, p.2]) := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a 0, a 1), ?_⟩
    change EisensteinWeightTwo.divisionEisensteinMF N hN ![a 0, a 1] =
      EisensteinWeightTwo.divisionEisensteinMF N hN a
    rw [← vector_eq_pair a]
  · rintro ⟨p, rfl⟩
    exact ⟨![p.1, p.2], rfl⟩

/-- The two independently specified series spans are equal by their actual generators. -/
theorem seriesSpan_eq_divisionSpan (N : ℕ) (hN : 0 < N) :
    DivisionEisensteinLevelMaps.seriesSpan N hN = divisionSpan N hN := by
  unfold DivisionEisensteinLevelMaps.seriesSpan divisionSpan
  rw [series_generator_ranges_eq]

/-- Positive upward restriction preserves the pair-indexed independent series span. -/
theorem restriction_mem_divisionSpan {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (hNL : N ∣ L)
    {f : WeightTwo N} (hf : f ∈ divisionSpan N hN) :
    DivisionEisensteinLevelMaps.restriction N L hNL f ∈ divisionSpan L hL := by
  rw [← seriesSpan_eq_divisionSpan N hN] at hf
  rw [← seriesSpan_eq_divisionSpan L hL]
  exact DivisionEisensteinLevelMaps.restriction_mem_seriesSpan hN hL hNL hf

/-- A correction list yields an actual modular form by restricting each genuine
finite defect-sum form upward and taking its weighted finite list sum. -/
def correctionForm (L : ℕ) (E : List Correction) (hE : ∀ T ∈ E, T.level ∣ L) : WeightTwo L :=
  match E with
  | [] => 0
  | T :: rest =>
    T.coeff • DivisionEisensteinLevelMaps.restriction T.level L (hE T (by simp))
      (DivisionSeriesCorrelation.defectSumForm T.level T.level_pos T.degree T.slope T.A T.B) +
    correctionForm L rest (fun U hU => hE U (List.mem_cons_of_mem T hU))

/-- Evaluation is exactly the explicit raw finite correction sum, including all zero classes. -/
theorem correctionForm_apply (L : ℕ) (E : List Correction) (hE : ∀ T ∈ E, T.level ∣ L) (τ : ℍ) :
    correctionForm L E hE τ = correctionSum τ E := by
  induction E with
  | nil => simp [correctionForm, correctionSum]
  | cons T E ih =>
    rw [correctionForm, add_apply, smul_apply,
      DivisionEisensteinLevelMaps.restriction_apply, DivisionSeriesCorrelation.defectSumForm_apply,
      ih, correctionSum_cons]
    rfl

/-- The weighted restricted finite sum belongs to the independent series span. -/
theorem correctionForm_mem_divisionSpan {L : ℕ} (hL : 0 < L) (E : List Correction)
    (hE : ∀ T ∈ E, T.level ∣ L) : correctionForm L E hE ∈ divisionSpan L hL := by
  induction E with
  | nil => exact (divisionSpan L hL).zero_mem
  | cons T E ih =>
    rw [correctionForm]
    apply (divisionSpan L hL).add_mem
    · apply (divisionSpan L hL).smul_mem
      exact restriction_mem_divisionSpan T.level_pos hL (hE T (by simp))
        (DivisionSeriesCorrelation.defectSumForm_mem_divisionSpan T.level T.level_pos
          T.degree T.slope T.A T.B)
    · exact ih _

/-- The sharp canonical level for degree-n correlation corrections. -/
def canonicalLevel (n M : ℕ) : ℕ := (n - 1).factorial * M

lemma canonicalLevel_pos (n : ℕ) {M : ℕ} (hM : 0 < M) : 0 < canonicalLevel n M :=
  Nat.mul_pos (Nat.factorial_pos _) hM

/-- The actual common-level correction built from the constructive correction records. -/
def canonicalCorrectionForm (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (s : ℕ) (A B : Point M) : WeightTwo (canonicalLevel n M) :=
  correctionForm (canonicalLevel n M) (correctionTerms n hn M hM hnM s A B)
    (correctionTerms_bound n hn M hM hnM s A B)

/-- Its value is the generated correction list, not a correlation-minus-products definition. -/
theorem canonicalCorrectionForm_apply (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M)
    (hnM : n ∣ M) (s : ℕ) (A B : Point M) (τ : ℍ) :
    canonicalCorrectionForm n hn M hM hnM s A B τ =
      correctionSum τ (correctionTerms n hn M hM hnM s A B) :=
  correctionForm_apply _ _ _ τ

/-- Genuine independent-series membership at the sharp canonical level. -/
theorem canonicalCorrectionForm_mem (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M)
    (hnM : n ∣ M) (s : ℕ) (A B : Point M) :
    canonicalCorrectionForm n hn M hM hnM s A B ∈
      divisionSpan (canonicalLevel n M) (canonicalLevel_pos n hM) :=
  correctionForm_mem_divisionSpan (canonicalLevel_pos n hM) _ _

/-- A single actual weight-two modular correction for every natural-slope
correlation, with original-level integer-row products and coefficients ±n. -/
theorem correlation_with_modular_correction (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M)
    (hnM : n ∣ M) (s : ℕ) (A B : Point M) :
    ∃ rows : List WeightedRow, ∃ E : WeightTwo (canonicalLevel n M),
      E ∈ divisionSpan (canonicalLevel n M) (canonicalLevel_pos n hM) ∧
      (∀ τ : ℍ, C M τ n s A B = rowSum M τ A B rows + E τ) ∧
      (∀ T ∈ rows, ValidRows n s T.2) ∧
      (∀ T ∈ rows, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ)) := by
  refine ⟨rowTerms n hn s, canonicalCorrectionForm n hn M hM hnM s A B,
    canonicalCorrectionForm_mem n hn M hM hnM s A B, ?_,
    rowTerms_valid n hn s, rowTerms_coeff n hn s⟩
  intro τ
  rw [canonicalCorrectionForm_apply]
  exact (correlation_rows n hn M hM hnM τ s A B).1

/-- The same correction lies in the vector-indexed series span through the proved range bridge. -/
theorem canonicalCorrectionForm_mem_seriesSpan (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M)
    (hnM : n ∣ M) (s : ℕ) (A B : Point M) :
    canonicalCorrectionForm n hn M hM hnM s A B ∈
      DivisionEisensteinLevelMaps.seriesSpan (canonicalLevel n M) (canonicalLevel_pos n hM) := by
  rw [seriesSpan_eq_divisionSpan]
  exact canonicalCorrectionForm_mem n hn M hM hnM s A B

/-- At original ambient nℓ the genuine modular correction has exactly level n!ℓ. -/
lemma canonicalLevel_paper {n : ℕ} (hn : 0 < n) (ℓ : ℕ) : canonicalLevel n (n * ℓ) = n.factorial * ℓ :=
  correction_bound_paper hn ℓ

/-- The natural-slope actual correlation statement at the paper's sharp level. -/
theorem correlation_paper_level (n ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ)
    (s : ℕ) (A B : Point (n * ℓ)) :
    ∃ rows : List WeightedRow, ∃ E : WeightTwo (n.factorial * ℓ),
      E ∈ divisionSpan (n.factorial * ℓ) (Nat.mul_pos (Nat.factorial_pos n) hℓ) ∧
      (∀ τ : ℍ, C (n * ℓ) τ n s A B = rowSum (n * ℓ) τ A B rows + E τ) ∧
      (∀ T ∈ rows, ValidRows n s T.2) ∧
      (∀ T ∈ rows, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ)) := by
  obtain ⟨rows, E, hE, hvalue, hrows, hcoeff⟩ := correlation_with_modular_correction n hn (n * ℓ)
    (Nat.mul_pos hn hℓ) (dvd_mul_right n ℓ) s A B
  have hpaper : 0 < n.factorial * ℓ := Nat.mul_pos (Nat.factorial_pos n) hℓ
  have hdiv : canonicalLevel n (n * ℓ) ∣ n.factorial * ℓ := by
    rw [canonicalLevel_paper hn ℓ]
  refine ⟨rows, DivisionEisensteinLevelMaps.restriction _ _ hdiv E,
    restriction_mem_divisionSpan (canonicalLevel_pos n (Nat.mul_pos hn hℓ)) hpaper hdiv hE,
    ?_, hrows, hcoeff⟩
  intro τ
  rw [DivisionEisensteinLevelMaps.restriction_apply]
  exact hvalue τ

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationModular
