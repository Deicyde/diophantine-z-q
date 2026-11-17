import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationEnlarge

/-!
# Original-level integer matrix rows for torsion correlations

Exact integer quotients transport the recursive product rows to the original
ambient group. The actual defect corrections are retained separately; no
Eisenstein or spanning assertion is made.
-/

noncomputable section

open Complex Function Set Finset
open scoped Real UpperHalfPlane BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationRows

open TorsionCorrelation TorsionCorrelationEnlarge

/-- The two integer rows of a product matrix. -/
structure Rows where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

/-- The determinant in the original integer row convention. -/
def Rows.det (R : Rows) : ℤ := R.a * R.d - R.b * R.c

/-- The exact determinant and the two original slope congruences. -/
def ValidRows (n s : ℕ) (R : Rows) : Prop :=
  (R.det = (n : ℤ) ∨ R.det = -(n : ℤ)) ∧
    (n : ℤ) ∣ R.a - (s : ℤ) * R.b ∧ (n : ℤ) ∣ R.c - (s : ℤ) * R.d

/-- The original-level actual h-product exhibited by the rows. -/
def rowValue (M : ℕ) (τ : ℍ) (A B : Point M) (R : Rows) : ℂ :=
  h M τ (R.a • A + R.b • B) * h M τ (R.c • A + R.d • B)

def baseRows (n : ℕ) : Rows := ⟨n, 0, 0, 1⟩
def firstRows (n r : ℕ) : Rows := ⟨n, 0, r, 1⟩

/-- The quotient coefficients are integers; exactness is proved for valid child rows. -/
def transportRows (n r : ℕ) (R : Rows) : Rows :=
  ⟨R.a, (R.a - (n : ℤ) * R.b) / (r : ℤ),
    R.c, (R.c - (n : ℤ) * R.d) / (r : ℤ)⟩

lemma remainder_difference (n s : ℕ) : (n : ℤ) ∣ ((s % n : ℕ) : ℤ) - (s : ℤ) := by
  refine ⟨-((s / n : ℕ) : ℤ), ?_⟩
  have hh : ((s % n : ℕ) : ℤ) + (n : ℤ) * ((s / n : ℕ) : ℤ) = (s : ℤ) := by
    exact_mod_cast Nat.mod_add_div s n
  linear_combination hh

lemma baseRows_valid {n s : ℕ} (hz : s % n = 0) : ValidRows n s (baseRows n) := by
  have hc := remainder_difference n s
  rw [hz, Nat.cast_zero, zero_sub] at hc
  refine ⟨Or.inl ?_, ?_, ?_⟩
  · simp [Rows.det, baseRows]
  · simp [baseRows]
  · simpa [baseRows] using hc

lemma firstRows_valid (n s : ℕ) : ValidRows n s (firstRows n (s % n)) := by
  refine ⟨Or.inl ?_, ?_, ?_⟩
  · simp [Rows.det, firstRows]
  · simp [firstRows]
  · simpa [firstRows] using remainder_difference n s

/-- Both row quotients are exact signed integer divisions, not natural truncations. -/
theorem transportRows_exact {n r : ℕ} {R : Rows} (hv : ValidRows r n R) :
    (r : ℤ) * (transportRows n r R).b = R.a - (n : ℤ) * R.b ∧
    (r : ℤ) * (transportRows n r R).d = R.c - (n : ℤ) * R.d := by
  exact ⟨Int.mul_ediv_cancel' hv.2.1, Int.mul_ediv_cancel' hv.2.2⟩

/-- Recursive rows acquire determinant ±n and the original slope congruences. -/
theorem transportRows_valid {n r s : ℕ} (hr : 0 < r)
    (hcong : (n : ℤ) ∣ (r : ℤ) - (s : ℤ)) {R : Rows}
    (hv : ValidRows r n R) : ValidRows n s (transportRows n r R) := by
  have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨hb, hd⟩ := transportRows_exact hv
  have hkey : (r : ℤ) * ((transportRows n r R).det) = -(n : ℤ) * R.det := by
    dsimp [Rows.det, transportRows] at hb hd ⊢
    linear_combination R.a * hd - R.c * hb
  have hdet : (transportRows n r R).det = (n : ℤ) ∨
      (transportRows n r R).det = -(n : ℤ) := by
    rcases hv.1 with hvdet | hvdet
    · right
      apply (mul_right_inj' hrZ).mp
      rw [hkey, hvdet]
      ring
    · left
      apply (mul_right_inj' hrZ).mp
      rw [hkey, hvdet]
      ring
  have ha : (n : ℤ) ∣ R.a - (r : ℤ) * (transportRows n r R).b := by
    refine ⟨R.b, ?_⟩
    linear_combination -hb
  have hc : (n : ℤ) ∣ R.c - (r : ℤ) * (transportRows n r R).d := by
    refine ⟨R.d, ?_⟩
    linear_combination -hd
  refine ⟨hdet, ?_, ?_⟩
  · change (n : ℤ) ∣ R.a - (s : ℤ) * (transportRows n r R).b
    rw [show R.a - (s : ℤ) * (transportRows n r R).b =
      (R.a - (r : ℤ) * (transportRows n r R).b) +
        ((r : ℤ) - (s : ℤ)) * (transportRows n r R).b by ring]
    exact dvd_add ha (dvd_mul_of_dvd_left hcong _)
  · change (n : ℤ) ∣ R.c - (s : ℤ) * (transportRows n r R).d
    rw [show R.c - (s : ℤ) * (transportRows n r R).d =
      (R.c - (r : ℤ) * (transportRows n r R).d) +
        ((r : ℤ) - (s : ℤ)) * (transportRows n r R).d by ring]
    exact dvd_add hc (dvd_mul_of_dvd_left hcong _)

/-- A single exact quotient row is the embedded original-level point. -/
theorem point_transport {M n r : ℕ} (hM : 0 < M) (a b : ℤ)
    (hdiv : (r : ℤ) ∣ a - (n : ℤ) * b) (A B : Point M) :
    a • (levelMap r M hM A + rootPoint r M B) + b • (-(n • rootPoint r M B)) =
      levelMap r M hM (a • A + ((a - (n : ℤ) * b) / (r : ℤ)) • B) := by
  let q : ℤ := (a - (n : ℤ) * b) / (r : ℤ)
  have hq : (r : ℤ) * q = a - (n : ℤ) * b := Int.mul_ediv_cancel' hdiv
  have hroot : (r : ℤ) • rootPoint r M B = levelMap r M hM B := by
    simpa only [natCast_zsmul] using rootPoint_spec hM r B
  have hterm : a • (levelMap r M hM A + rootPoint r M B) + b • (-(n • rootPoint r M B)) =
      a • levelMap r M hM A + (a - (n : ℤ) * b) • rootPoint r M B := by
    simp only [← natCast_zsmul]
    module
  change a • (levelMap r M hM A + rootPoint r M B) + b • (-(n • rootPoint r M B)) =
    levelMap r M hM (a • A + q • B)
  rw [hterm, ← hq, mul_comm (r : ℤ) q, mul_zsmul, hroot]
  rw [map_add, map_zsmul, map_zsmul]

/-- Both actual h-factors of a valid child product pull back to the original M. -/
theorem rowValue_transport {M n r : ℕ} (hM : 0 < M) (hr : 0 < r) (τ : ℍ)
    (A B : Point M) (R : Rows) (hv : ValidRows r n R) :
    rowValue (r * M) τ (levelMap r M hM A + rootPoint r M B) (-(n • rootPoint r M B)) R =
      rowValue M τ A B (transportRows n r R) := by
  unfold rowValue
  rw [point_transport hM R.a R.b hv.2.1, point_transport hM R.c R.d hv.2.2]
  rw [h_levelMap hr hM, h_levelMap hr hM]
  rfl

lemma baseRows_value (M : ℕ) (τ : ℍ) (A B : Point M) (n : ℕ) :
    rowValue M τ A B (baseRows n) = h M τ (n • A) * h M τ B := by
  simp [rowValue, baseRows]

lemma firstRows_value (M : ℕ) (τ : ℍ) (A B : Point M) (n r : ℕ) :
    rowValue M τ A B (firstRows n r) = h M τ (n • A) * h M τ (r • A + B) := by
  simp [rowValue, firstRows]

abbrev WeightedRow := ℂ × Rows

/-- Evaluation of an explicitly finite complex linear combination at the original level. -/
def rowSum (M : ℕ) (τ : ℍ) (A B : Point M) (L : List WeightedRow) : ℂ :=
  (L.map (fun T => T.1 * rowValue M τ A B T.2)).sum

def transportWeighted (n r : ℕ) (c : ℂ) (T : WeightedRow) : WeightedRow :=
  (c * T.1, transportRows n r T.2)

/-- Constructive original-level row witnesses for every natural slope. -/
def rowTerms (n : ℕ) (_hn : 0 < n) (s : ℕ) : List WeightedRow :=
  if hz : s % n = 0 then
    [((n : ℂ), baseRows n)]
  else
    let r := s % n
    have hr : 0 < r := Nat.pos_of_ne_zero hz
    ((n : ℂ), firstRows n r) ::
      (rowTerms r hr n).map (transportWeighted n r (-(n : ℂ) / (r : ℂ)))
termination_by n
decreasing_by exact Nat.mod_lt s _hn

/-- Every generated integer matrix has the exact original determinant and congruences. -/
theorem rowTerms_valid (n : ℕ) (hn : 0 < n) (s : ℕ) :
    ∀ T ∈ rowTerms n hn s, ValidRows n s T.2 := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rw [rowTerms]
    split_ifs with hz
    · intro T hT
      simp only [List.mem_singleton] at hT
      subst T
      exact baseRows_valid hz
    · dsimp only
      intro T hT
      rcases List.mem_cons.mp hT with hT | hT
      · subst T
        exact firstRows_valid n s
      · obtain ⟨U, hU, hTU⟩ := List.mem_map.mp hT
        subst T
        exact transportRows_valid (Nat.pos_of_ne_zero hz) (remainder_difference n s)
          (ih (s % n) (Nat.mod_lt s hn) (Nat.pos_of_ne_zero hz) n U hU)

/-- A correction record describes a genuine finite D-sum at its actual positive level. -/
structure Correction where
  level : ℕ
  level_pos : 0 < level
  degree : ℕ
  slope : ℕ
  degree_pos : 0 < degree
  slope_pos : 0 < slope
  degree_dvd : degree ∣ level
  slope_dvd : slope ∣ level
  A : Point level
  B : Point level
  coeff : ℂ

/-- Explicit finite correction evaluation, never defined by subtracting a product sum from C. -/
def correctionSum (τ : ℍ) (L : List Correction) : ℂ :=
  (L.map (fun T => T.coeff * defectSum T.level τ T.degree T.slope T.A T.B)).sum

def weightCorrection (c : ℂ) (T : Correction) : Correction := { T with coeff := c * T.coeff }

def firstCorrection (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (r : ℕ) (hr : 0 < r) (A B : Point M) : Correction where
  level := r * M
  level_pos := Nat.mul_pos hr hM
  degree := n
  slope := r
  degree_pos := hn
  slope_pos := hr
  degree_dvd := dvd_mul_of_dvd_right hnM r
  slope_dvd := dvd_mul_right r M
  A := levelMap r M hM A
  B := rootPoint r M B
  coeff := 1 / (r : ℂ)

/-- Actual correction witnesses, with every level and point retained. -/
def correctionTerms (n : ℕ) (_hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (s : ℕ) (A B : Point M) : List Correction :=
  if hz : s % n = 0 then [] else
    let r := s % n
    have hr : 0 < r := Nat.pos_of_ne_zero hz
    firstCorrection n _hn M hM hnM r hr A B ::
      (correctionTerms r hr (r * M) (Nat.mul_pos hr hM) (dvd_mul_right r M) n
        (levelMap r M hM A + rootPoint r M B) (-(n • rootPoint r M B))).map
          (weightCorrection (-(n : ℂ) / (r : ℂ)))
termination_by n
decreasing_by exact Nat.mod_lt s _hn

lemma rowSum_cons (M : ℕ) (τ : ℍ) (A B : Point M) (T : WeightedRow) (L : List WeightedRow) :
    rowSum M τ A B (T :: L) = T.1 * rowValue M τ A B T.2 + rowSum M τ A B L := by
  simp [rowSum]

lemma correctionSum_cons (τ : ℍ) (T : Correction) (L : List Correction) :
    correctionSum τ (T :: L) = T.coeff * defectSum T.level τ T.degree T.slope T.A T.B +
      correctionSum τ L := by simp [correctionSum]

lemma correctionSum_weight (τ : ℍ) (c : ℂ) (L : List Correction) :
    correctionSum τ (L.map (weightCorrection c)) = c * correctionSum τ L := by
  unfold correctionSum
  rw [List.map_map]
  change (L.map (fun T => c * T.coeff * defectSum T.level τ T.degree T.slope T.A T.B)).sum = _
  simp_rw [mul_assoc]
  exact List.sum_map_mul_left L _ c

/-- The weighted recursive row sum is transported by actual point and h-value identities. -/
theorem rowSum_transport {M n r : ℕ} (hM : 0 < M) (hr : 0 < r) (τ : ℍ)
    (A B : Point M) (c : ℂ) (L : List WeightedRow)
    (hL : ∀ T ∈ L, ValidRows r n T.2) :
    rowSum M τ A B (L.map (transportWeighted n r c)) =
      c * rowSum (r * M) τ (levelMap r M hM A + rootPoint r M B)
        (-(n • rootPoint r M B)) L := by
  unfold rowSum
  rw [List.map_map]
  have hm : L.map (fun T => c * T.1 * rowValue M τ A B (transportRows n r T.2)) =
      L.map (fun T => c * (T.1 * rowValue (r * M) τ
        (levelMap r M hM A + rootPoint r M B) (-(n • rootPoint r M B)) T.2)) := by
    apply List.map_congr_left
    intro T hT
    rw [← rowValue_transport hM hr τ A B T.2 (hL T hT)]
    ring
  change (L.map (fun T => c * T.1 * rowValue M τ A B (transportRows n r T.2))).sum = _
  rw [hm, List.sum_map_mul_left]

lemma factorial_pred_mul {r : ℕ} (hr : 0 < r) : (r - 1).factorial * r = r.factorial := by
  cases r with
  | zero => omega
  | succ r => simp [Nat.factorial_succ, Nat.mul_comm]

/-- Every described correction level divides the sharp canonical factorial bound. -/
theorem correctionTerms_bound (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (s : ℕ) (A B : Point M) :
    ∀ T ∈ correctionTerms n hn M hM hnM s A B, T.level ∣ (n - 1).factorial * M := by
  induction n using Nat.strong_induction_on generalizing M s with
  | h n ih =>
    rw [correctionTerms]
    split_ifs with hz
    · simp
    · dsimp only
      have hr : 0 < s % n := Nat.pos_of_ne_zero hz
      have hlt : s % n < n := Nat.mod_lt s hn
      have hfac : (s % n).factorial ∣ (n - 1).factorial :=
        Nat.factorial_dvd_factorial (by omega)
      intro T hT
      rcases List.mem_cons.mp hT with hT | hT
      · subst T
        exact mul_dvd_mul ((Nat.dvd_factorial hr le_rfl).trans hfac) (dvd_refl M)
      · obtain ⟨U, hU, hTU⟩ := List.mem_map.mp hT
        subst T
        have hbound := ih (s % n) hlt hr ((s % n) * M) (Nat.mul_pos hr hM)
          (dvd_mul_right (s % n) M) n
          (levelMap (s % n) M hM A + rootPoint (s % n) M B)
          (-(n • rootPoint (s % n) M B)) U hU
        rw [← Nat.mul_assoc, factorial_pred_mul hr] at hbound
        exact hbound.trans (mul_dvd_mul hfac (dvd_refl M))

/-- The actual finite expansion splits into original-level constrained row products
and the separately described finite correction records. -/
theorem expansion_rows (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (τ : ℍ) (s : ℕ) (A B : Point M) :
    euclideanExpansion n hn M hM hnM τ s A B =
      rowSum M τ A B (rowTerms n hn s) + correctionSum τ (correctionTerms n hn M hM hnM s A B) := by
  induction n using Nat.strong_induction_on generalizing M s with
  | h n ih =>
    rw [euclideanExpansion, rowTerms, correctionTerms]
    split_ifs with hz
    · simp [rowSum, correctionSum, baseRows_value, mul_assoc]
    · dsimp only
      have hr : 0 < s % n := Nat.pos_of_ne_zero hz
      have hlt : s % n < n := Nat.mod_lt s hn
      have hi := ih (s % n) hlt hr ((s % n) * M) (Nat.mul_pos hr hM)
        (dvd_mul_right (s % n) M) n
        (levelMap (s % n) M hM A + rootPoint (s % n) M B) (-(n • rootPoint (s % n) M B))
      rw [hi, rowSum_cons, correctionSum_cons]
      rw [rowSum_transport hM hr τ A B (-(n : ℂ) / ((s % n : ℕ) : ℂ))
        (rowTerms (s % n) hr n) (rowTerms_valid (s % n) hr n)]
      rw [correctionSum_weight, firstRows_value]
      dsimp only [firstCorrection]
      ring

/-- Full actual original-level finite product witnesses, with exact integer
matrix constraints and every explicit correction level bounded. -/
theorem correlation_rows (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (τ : ℍ) (s : ℕ) (A B : Point M) :
    C M τ n s A B = rowSum M τ A B (rowTerms n hn s) +
      correctionSum τ (correctionTerms n hn M hM hnM s A B) ∧
      (∀ T ∈ rowTerms n hn s, ValidRows n s T.2) ∧
      (∀ T ∈ correctionTerms n hn M hM hnM s A B, T.level ∣ (n - 1).factorial * M) := by
  refine ⟨?_, rowTerms_valid n hn s, correctionTerms_bound n hn M hM hnM s A B⟩
  rw [← euclideanExpansion_eq_C n hn M hM hnM τ s A B]
  exact expansion_rows n hn M hM hnM τ s A B

/-- At ambient M=nℓ the correction bound is exactly the paper's n!ℓ. -/
lemma correction_bound_paper {n : ℕ} (hn : 0 < n) (ℓ : ℕ) :
    (n - 1).factorial * (n * ℓ) = n.factorial * ℓ := by
  rw [← Nat.mul_assoc, factorial_pred_mul hn]

/-- Every uncollected product coefficient is exactly plus or minus n. -/
theorem rowTerms_coeff (n : ℕ) (hn : 0 < n) (s : ℕ) :
    ∀ T ∈ rowTerms n hn s, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ) := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rw [rowTerms]
    split_ifs with hz
    · intro T hT
      simp only [List.mem_singleton] at hT
      subst T
      exact Or.inl rfl
    · dsimp only
      have hr : 0 < s % n := Nat.pos_of_ne_zero hz
      have hrC : ((s % n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      intro T hT
      rcases List.mem_cons.mp hT with hT | hT
      · subst T
        exact Or.inl rfl
      · obtain ⟨U, hU, hTU⟩ := List.mem_map.mp hT
        subst T
        rcases ih (s % n) (Nat.mod_lt s hn) hr n U hU with hc | hc
        · right
          change (-(n : ℂ) / ((s % n : ℕ) : ℂ)) * U.1 = -(n : ℂ)
          rw [hc]
          field_simp [hrC]
        · left
          change (-(n : ℂ) / ((s % n : ℕ) : ℂ)) * U.1 = (n : ℂ)
          rw [hc]
          field_simp [hrC]

/-- Explicit finite witnesses for the actual original-level row combination
and the positively leveled, numerically bounded D-corrections. -/
theorem correlation_rows_exists (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (τ : ℍ) (s : ℕ) (A B : Point M) :
    ∃ L : List WeightedRow, ∃ E : List Correction,
      C M τ n s A B = rowSum M τ A B L + correctionSum τ E ∧
      (∀ T ∈ L, ValidRows n s T.2) ∧
      (∀ T ∈ L, T.1 = (n : ℂ) ∨ T.1 = -(n : ℂ)) ∧
      (∀ T ∈ E, T.level ∣ (n - 1).factorial * M) := by
  refine ⟨rowTerms n hn s, correctionTerms n hn M hM hnM s A B, ?_,
    rowTerms_valid n hn s, rowTerms_coeff n hn s, correctionTerms_bound n hn M hM hnM s A B⟩
  exact (correlation_rows n hn M hM hnM τ s A B).1

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationRows
