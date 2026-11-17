import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationLower
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan

/-!
# Original lower-level products and the actual canonical series correction

The raw products are genuine admissible torsion products or zero. Each
independent division-series generator is identified with its proved actual
quadratic generator. The canonical upper correction is the restriction of
a genuine lower modular error, without asserting downward series closure.
-/

noncomputable section

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationLowerProducts

open TorsionCorrelation TorsionCorrelationEnlarge TorsionCorrelationRows
open TorsionCorrelationModular TorsionCorrelationSigned TorsionCorrelationLower DivisionSeriesMembership

/-- Every actual raw product at a positive level is an admissible degree-two product or zero. -/
theorem rawProductForm_mem_productSpan (M : ℕ) (hM : 0 < M) (P Q : Point M) :
    rawProductForm M hM P Q ∈ TorsionQuadraticGenerators.productSpan M hM := by
  obtain ⟨a,b,rfl⟩ := label_surjective hM P
  obtain ⟨c,d,rfl⟩ := label_surjective hM Q
  by_cases hp : (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b
  · have hz : rawProductForm M hM (label M a b) (label M c d) = 0 := by
      apply _root_.ModularForm.ext
      intro τ
      rw [rawProductForm_apply, h_label hM, TorsionDistributionTwo.reg_of_bad hp]
      simp
    rw [hz]
    exact (TorsionQuadraticGenerators.productSpan M hM).zero_mem
  · by_cases hq : (M : ℤ) ∣ c ∧ (M : ℤ) ∣ d
    · have hz : rawProductForm M hM (label M a b) (label M c d) = 0 := by
        apply _root_.ModularForm.ext
        intro τ
        rw [rawProductForm_apply, h_label hM, h_label hM, TorsionDistributionTwo.reg_of_bad hq]
        simp
      rw [hz]
      exact (TorsionQuadraticGenerators.productSpan M hM).zero_mem
    · let v : Fin 2 → ℤ × ℤ := ![(a,b),(c,d)]
      have hv : ∀ i, AllLevelForms.Good M (v i) := by
        intro i
        fin_cases i
        · exact hp
        · exact hq
      have heq : rawProductForm M hM (label M a b) (label M c d) =
          AllLevelProducts.productForm M hM 2 v hv := by
        apply _root_.ModularForm.ext
        intro τ
        rw [rawProductForm_apply, h_label hM, h_label hM,
          TorsionDistributionTwo.reg_of_good hp, TorsionDistributionTwo.reg_of_good hq,
          AllLevelProducts.productForm_apply]
        simp [v, Fin.prod_univ_two]
      exact Submodule.subset_span ⟨v,hv,heq⟩

/-- A row's actual product as a lower-level modular form. -/
def rowForm (M : ℕ) (hM : 0 < M) (A B : Point M) (R : Rows) : WeightTwo M :=
  rawProductForm M hM (R.a • A + R.b • B) (R.c • A + R.d • B)

lemma rowForm_apply (M : ℕ) (hM : 0 < M) (A B : Point M) (R : Rows) (τ : ℍ) :
    rowForm M hM A B R τ = rowValue M τ A B R := rawProductForm_apply _ _ _ _ τ

/-- The finite original-level row sum as a genuine modular form. -/
def rowSumForm (M : ℕ) (hM : 0 < M) (A B : Point M) : List WeightedRow → WeightTwo M
  | [] => 0
  | T :: rest => T.1 • rowForm M hM A B T.2 + rowSumForm M hM A B rest

lemma rowSumForm_apply (M : ℕ) (hM : 0 < M) (A B : Point M) (L : List WeightedRow) (τ : ℍ) :
    rowSumForm M hM A B L τ = rowSum M τ A B L := by
  induction L with
  | nil => simp [rowSumForm, rowSum]
  | cons T L ih =>
    rw [rowSumForm, add_apply, smul_apply, rowForm_apply, ih, rowSum_cons]
    rfl

/-- Every actual original-level row sum lies in the genuine admissible product span. -/
theorem rowSumForm_mem_productSpan (M : ℕ) (hM : 0 < M) (A B : Point M) (L : List WeightedRow) :
    rowSumForm M hM A B L ∈ TorsionQuadraticGenerators.productSpan M hM := by
  induction L with
  | nil => exact (TorsionQuadraticGenerators.productSpan M hM).zero_mem
  | cons T L ih =>
    rw [rowSumForm]
    exact (TorsionQuadraticGenerators.productSpan M hM).add_mem
      ((TorsionQuadraticGenerators.productSpan M hM).smul_mem _
        (rawProductForm_mem_productSpan M hM _ _)) ih

/-- Embedded original-level integer rows preserve both actual h-values. -/
theorem rowValue_levelMap {M k : ℕ} (hM : 0 < M) (hk : 0 < k) (τ : ℍ)
    (A B : Point M) (R : Rows) :
    rowValue (k * M) τ (levelMap k M hM A) (levelMap k M hM B) R = rowValue M τ A B R := by
  unfold rowValue
  have hp : R.a • levelMap k M hM A + R.b • levelMap k M hM B =
      levelMap k M hM (R.a • A + R.b • B) := by rw [map_add, map_zsmul, map_zsmul]
  have hq : R.c • levelMap k M hM A + R.d • levelMap k M hM B =
      levelMap k M hM (R.c • A + R.d • B) := by rw [map_add, map_zsmul, map_zsmul]
  rw [hp, hq, h_levelMap hk hM, h_levelMap hk hM]

lemma rowSum_levelMap {M k : ℕ} (hM : 0 < M) (hk : 0 < k) (τ : ℍ)
    (A B : Point M) (L : List WeightedRow) :
    rowSum (k * M) τ (levelMap k M hM A) (levelMap k M hM B) L = rowSum M τ A B L := by
  unfold rowSum
  simp_rw [rowValue_levelMap hM hk]

/-- Each genuine independent series form equals the proved actual quadratic x-form at level at least three. -/
theorem series_generator_eq_quadratic (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a : Fin 2 → ℤ) :
    EisensteinWeightTwo.divisionEisensteinMF N hN a = TorsionQuadraticGenerators.xForm N h3 (a 0) (a 1) := by
  have : NeZero N := ⟨hN.ne'⟩
  apply _root_.ModularForm.ext
  intro τ
  have hx := EisensteinWeightTwo.divisionEisensteinMF_eq_xValue_all N hN (a 0) (a 1) τ
  rw [← TorsionCorrelationModular.vector_eq_pair a] at hx
  rw [hx, TorsionQuadraticGenerators.xForm_apply]

/-- The independent series span is contained in the actual product span by its actual generators. -/
theorem divisionSpan_le_productSpan (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) :
    divisionSpan N hN ≤ TorsionQuadraticGenerators.productSpan N hN := by
  apply Submodule.span_le.mpr
  rintro f ⟨p,rfl⟩
  change EisensteinWeightTwo.divisionEisensteinMF N hN ![p.1,p.2] ∈
    TorsionQuadraticGenerators.productSpan N hN
  rw [series_generator_eq_quadratic N hN h3 ![p.1,p.2]]
  exact TorsionQuadraticGenerators.xForm_mem_productSpan N h3 p.1 p.2

/-- The actual upper canonical correction for the embedded lower-level correlation. -/
def upperErrorForm (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ) (A B : Point ℓ) :
    WeightTwo (canonicalLevel n (n * ℓ)) :=
  canonicalCorrectionForm n hn (n * ℓ) (Nat.mul_pos hn hℓ) (dvd_mul_right n ℓ)
    (residue n s) (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B)

/-- Its independently proved upper series-span membership. -/
theorem upperErrorForm_mem_seriesSpan (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ) (A B : Point ℓ) :
    upperErrorForm ℓ n hℓ hn s A B ∈
      DivisionEisensteinLevelMaps.seriesSpan (canonicalLevel n (n * ℓ))
        (canonicalLevel_pos n (Nat.mul_pos hn hℓ)) :=
  canonicalCorrectionForm_mem_seriesSpan _ _ _ _ _ _ _ _

/-- A genuine lower modular error whose restriction equals the already constructed canonical correction. -/
def lowerErrorForm (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ) (A B : Point ℓ) : WeightTwo ℓ :=
  lowerCorrelationForm ℓ n hℓ hn s A B - rowSumForm ℓ hℓ A B (rowTerms n hn (residue n s))

/-- The lower error's value is proved equal to the explicit canonical finite correction. -/
theorem lowerErrorForm_apply (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ)
    (A B : Point ℓ) (τ : ℍ) :
    lowerErrorForm ℓ n hℓ hn s A B τ = upperErrorForm ℓ n hℓ hn s A B τ := by
  have hh := signed_canonical_identity n hn (n * ℓ) (Nat.mul_pos hn hℓ) (dvd_mul_right n ℓ)
    s (levelMap n ℓ hℓ A) (levelMap n ℓ hℓ B) τ
  rw [rowSum_levelMap hℓ hn] at hh
  change lowerCorrelationForm ℓ n hℓ hn s A B τ - rowSumForm ℓ hℓ A B (rowTerms n hn (residue n s)) τ = _
  rw [lowerCorrelationForm_apply, rowSumForm_apply]
  apply sub_eq_iff_eq_add.mpr
  simpa only [upperErrorForm, add_comm] using hh

/-- The constructed canonical correction is genuinely invariant under the lower principal group. -/
theorem upperErrorForm_invariant (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ) (A B : Point ℓ) :
    ∀ γ ∈ (CongruenceSubgroup.Gamma ℓ).map (Matrix.SpecialLinearGroup.mapGL ℝ),
      ⇑(upperErrorForm ℓ n hℓ hn s A B) ∣[(2 : ℤ)] γ = ⇑(upperErrorForm ℓ n hℓ hn s A B) := by
  have heq : ⇑(upperErrorForm ℓ n hℓ hn s A B) = ⇑(lowerErrorForm ℓ n hℓ hn s A B) :=
    funext fun τ => (lowerErrorForm_apply ℓ n hℓ hn s A B τ).symm
  rw [heq]
  exact (lowerErrorForm ℓ n hℓ hn s A B).slash_action_eq'

lemma lower_level_dvd_canonical (ℓ n : ℕ) : ℓ ∣ canonicalLevel n (n * ℓ) :=
  dvd_mul_of_dvd_right (dvd_mul_left ℓ n) (n - 1).factorial

/-- Actual restriction equality, with no lower-series membership premise or conclusion. -/
theorem lowerErrorForm_restriction (ℓ n : ℕ) (hℓ : 0 < ℓ) (hn : 0 < n) (s : ℤ) (A B : Point ℓ) :
    DivisionEisensteinLevelMaps.restriction ℓ (canonicalLevel n (n * ℓ)) (lower_level_dvd_canonical ℓ n)
      (lowerErrorForm ℓ n hℓ hn s A B) = upperErrorForm ℓ n hℓ hn s A B := by
  apply _root_.ModularForm.ext
  intro τ
  rw [DivisionEisensteinLevelMaps.restriction_apply, lowerErrorForm_apply]

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationLowerProducts
