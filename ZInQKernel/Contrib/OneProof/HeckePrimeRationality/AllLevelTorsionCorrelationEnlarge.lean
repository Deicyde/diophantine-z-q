import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelation

/-!
# True ambient enlargement and modular slope reduction

The actual torsion function, correlations and defect corrections are
transported by an injective additive level map. Preimages are constructed
in an enlarged level, never asserted to exist in the original level.
-/

noncomputable section

open Complex Set Function Finset
open scoped Real UpperHalfPlane BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationEnlarge

open TorsionCorrelation

/-- Scaling integer representatives respects residue-class equality. -/
lemma scaled_label_congr (k M : ℕ) (a b c d : ℤ)
    (heq : label M a b = label M c d) :
    label (k * M) ((k : ℤ) * a) ((k : ℤ) * b) =
      label (k * M) ((k : ℤ) * c) ((k : ℤ) * d) := by
  have ha := (ZMod.intCast_eq_intCast_iff_dvd_sub a c M).mp (congrArg Prod.fst heq)
  have hb := (ZMod.intCast_eq_intCast_iff_dvd_sub b d M).mp (congrArg Prod.snd heq)
  apply Prod.ext
  · apply (ZMod.intCast_eq_intCast_iff_dvd_sub ((k : ℤ) * a) ((k : ℤ) * c) (k * M)).mpr
    push_cast
    rw [show (k : ℤ) * c - (k : ℤ) * a = (k : ℤ) * (c - a) by ring]
    exact mul_dvd_mul (dvd_refl (k : ℤ)) ha
  · apply (ZMod.intCast_eq_intCast_iff_dvd_sub ((k : ℤ) * b) ((k : ℤ) * d) (k * M)).mpr
    push_cast
    rw [show (k : ℤ) * d - (k : ℤ) * b = (k : ℤ) * (d - b) by ring]
    exact mul_dvd_mul (dvd_refl (k : ℤ)) hb

/-- The actual coordinate map to the multiplied ambient level. -/
def scaledPoint (k M : ℕ) (P : Point M) : Point (k * M) :=
  label (k * M) ((k : ℤ) * (P.1.val : ℤ)) ((k : ℤ) * (P.2.val : ℤ))

lemma scaledPoint_label {M : ℕ} (hM : 0 < M) (k : ℕ) (a b : ℤ) :
    scaledPoint k M (label M a b) = label (k * M) ((k : ℤ) * a) ((k : ℤ) * b) := by
  unfold scaledPoint
  exact scaled_label_congr k M _ _ a b (label_val hM (label M a b))

lemma scaledPoint_zero {M : ℕ} (hM : 0 < M) (k : ℕ) : scaledPoint k M 0 = 0 := by
  rw [show (0 : Point M) = label M 0 0 by apply Prod.ext <;> simp [label], scaledPoint_label hM]
  apply Prod.ext <;> simp [label]

lemma scaledPoint_add {M : ℕ} (hM : 0 < M) (k : ℕ) (P Q : Point M) :
    scaledPoint k M (P + Q) = scaledPoint k M P + scaledPoint k M Q := by
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  obtain ⟨c, d, rfl⟩ := label_surjective hM Q
  rw [label_add, scaledPoint_label hM, scaledPoint_label hM, scaledPoint_label hM, label_add]
  congr 1 <;> ring

/-- The additive level map. It is an embedding whenever k is positive. -/
def levelMap (k M : ℕ) (hM : 0 < M) : Point M →+ Point (k * M) where
  toFun := scaledPoint k M
  map_zero' := scaledPoint_zero hM k
  map_add' := scaledPoint_add hM k

lemma levelMap_label {M : ℕ} (hM : 0 < M) (k : ℕ) (a b : ℤ) :
    levelMap k M hM (label M a b) = label (k * M) ((k : ℤ) * a) ((k : ℤ) * b) :=
  scaledPoint_label hM k a b

/-- Positive level scaling cannot identify distinct original classes. -/
theorem levelMap_injective {k M : ℕ} (hk : 0 < k) (hM : 0 < M) :
    Function.Injective (levelMap k M hM) := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  intro P Q heq
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  obtain ⟨c, d, rfl⟩ := label_surjective hM Q
  rw [levelMap_label hM, levelMap_label hM] at heq
  have ha := (ZMod.intCast_eq_intCast_iff_dvd_sub ((k : ℤ) * a) ((k : ℤ) * c) (k * M)).mp
    (congrArg Prod.fst heq)
  have hb := (ZMod.intCast_eq_intCast_iff_dvd_sub ((k : ℤ) * b) ((k : ℤ) * d) (k * M)).mp
    (congrArg Prod.snd heq)
  push_cast at ha hb
  rw [show (k : ℤ) * c - (k : ℤ) * a = (k : ℤ) * (c - a) by ring] at ha
  rw [show (k : ℤ) * d - (k : ℤ) * b = (k : ℤ) * (d - b) by ring] at hb
  apply Prod.ext
  · exact (ZMod.intCast_eq_intCast_iff_dvd_sub a c M).mpr ((mul_dvd_mul_iff_left hkZ).mp ha)
  · exact (ZMod.intCast_eq_intCast_iff_dvd_sub b d M).mpr ((mul_dvd_mul_iff_left hkZ).mp hb)

/-- The actual zero-extended torsion value is preserved, including zero classes. -/
theorem h_levelMap {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (τ : ℍ) (P : Point M) :
    h (k * M) τ (levelMap k M hM P) = h M τ P := by
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  rw [levelMap_label hM, h_label (Nat.mul_pos hk hM), h_label hM, reg_scale k M hk hM]

/-- Enlargement carries the standard n-torsion embedding to the same actual points. -/
theorem levelMap_divisionPoint {M n : ℕ} (hM : 0 < M) (hnM : n ∣ M) (k : ℕ)
    (T : DivisionIndex n) :
    levelMap k M hM (divisionPoint M n T) = divisionPoint (k * M) n T := by
  unfold divisionPoint
  rw [levelMap_label hM, Nat.mul_div_assoc k hnM]
  congr 1 <;> push_cast <;> ring

/-- Exact transport of an actual quadratic defect; no membership claim is used. -/
theorem D_levelMap {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (τ : ℍ) (P Q : Point M) :
    D (k * M) τ (levelMap k M hM P) (levelMap k M hM Q) = D M τ P Q := by
  unfold D
  rw [← map_add]
  simp only [h_levelMap hk hM]

/-- Exact transport of the actual correlation to a larger ambient level. -/
theorem C_levelMap {k M n : ℕ} (hk : 0 < k) (hM : 0 < M) (hnM : n ∣ M)
    (τ : ℍ) (s : ℕ) (A B : Point M) :
    C (k * M) τ n s (levelMap k M hM A) (levelMap k M hM B) = C M τ n s A B := by
  unfold C
  apply Finset.sum_congr rfl
  intro T _
  have hA : levelMap k M hM A + divisionPoint (k * M) n T =
      levelMap k M hM (A + divisionPoint M n T) := by
    rw [map_add, levelMap_divisionPoint hM hnM]
  have hB : levelMap k M hM B - s • divisionPoint (k * M) n T =
      levelMap k M hM (B - s • divisionPoint M n T) := by
    rw [map_sub, map_nsmul, levelMap_divisionPoint hM hnM]
  rw [hA, hB, h_levelMap hk hM, h_levelMap hk hM]

/-- Exact transport of the entire double defect correction when both torsion groups embed. -/
theorem defectSum_levelMap {k M n s : ℕ} (hk : 0 < k) (hM : 0 < M)
    (hnM : n ∣ M) (hsM : s ∣ M) (τ : ℍ) (A B' : Point M) :
    defectSum (k * M) τ n s (levelMap k M hM A) (levelMap k M hM B') =
      defectSum M τ n s A B' := by
  unfold defectSum
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro U _
  have hP : levelMap k M hM A + divisionPoint (k * M) n T =
      levelMap k M hM (A + divisionPoint M n T) := by
    rw [map_add, levelMap_divisionPoint hM hnM]
  have hQ : levelMap k M hM B' - divisionPoint (k * M) n T + divisionPoint (k * M) s U =
      levelMap k M hM (B' - divisionPoint M n T + divisionPoint M s U) := by
    rw [map_add, map_sub, levelMap_divisionPoint hM hnM, levelMap_divisionPoint hM hsM]
  rw [hP, hQ, D_levelMap hk hM]

/-- A canonical integer-representative lift, choosing an s-preimage at level sM.
It is not asserted to be additive or to lie in the original level. -/
def rootPoint (s M : ℕ) (B : Point M) : Point (s * M) :=
  label (s * M) (B.1.val : ℤ) (B.2.val : ℤ)

/-- Every original class has the displayed preimage after the actual enlargement. -/
theorem rootPoint_spec {M : ℕ} (hM : 0 < M) (s : ℕ) (B : Point M) :
    s • rootPoint s M B = levelMap s M hM B := by
  unfold rootPoint
  rw [label_nsmul]
  rfl

/-- The actual correlation is periodic in its natural slope, from the killed torsion point. -/
theorem slope_period {M n : ℕ} (hnM : n ∣ M) (τ : ℍ) (s : ℕ) (A B : Point M) :
    C M τ n (s + n) A B = C M τ n s A B := by
  unfold C
  simp only [add_nsmul, divisionPoint_torsion hnM, add_zero]

/-- Only the slope modulo n matters, without a caller-supplied periodicity premise. -/
theorem slope_mod {M n : ℕ} (hnM : n ∣ M) (τ : ℍ) (s : ℕ) (A B : Point M) :
    C M τ n s A B = C M τ n (s % n) A B := by
  have hp : Function.Periodic (fun t : ℕ => C M τ n t A B) n :=
    fun t => slope_period hnM τ t A B
  have hh : C M τ n ((s % n) + (s / n) * n) A B = C M τ n (s % n) A B :=
    hp.nat_mul (s / n) (s % n)
  have he : (s % n) + (s / n) * n = s := by rw [Nat.mul_comm, Nat.mod_add_div]
  rwa [he] at hh

/-- Positive-degree slope reduction also supplies the strict remainder bound. -/
theorem slope_reduction {M n : ℕ} (hn : 0 < n) (hnM : n ∣ M) (τ : ℍ) (s : ℕ)
    (A B : Point M) : C M τ n s A B = C M τ n (s % n) A B ∧ s % n < n :=
  ⟨slope_mod hnM τ s A B, Nat.mod_lt s hn⟩

/-- The frozen actual recurrence is bound to the constructed preimage in sM.
The recursive correlation and defect remain explicitly at the larger level. -/
theorem enlarged_recurrence {M n s : ℕ} (hM : 0 < M) (hn : 0 < n) (hs : 0 < s)
    (hnM : n ∣ M) (τ : ℍ) (A B : Point M) :
    C M τ n s A B =
      (n : ℂ) * h M τ (n • A) * h M τ (s • A + B) -
      ((n : ℂ) / (s : ℂ)) * C (s * M) τ s n
        (levelMap s M hM A + rootPoint s M B) (-(n • rootPoint s M B)) +
      (1 / (s : ℂ)) * defectSum (s * M) τ n s (levelMap s M hM A) (rootPoint s M B) := by
  have hbig : 0 < s * M := Nat.mul_pos hs hM
  have hnBig : n ∣ s * M := dvd_mul_of_dvd_right hnM s
  have hsBig : s ∣ s * M := dvd_mul_right s M
  have hh := correlation_recurrence hbig hn hs hnBig hsBig τ
    (levelMap s M hM A) (levelMap s M hM B) (rootPoint s M B) (rootPoint_spec hM s B)
  rw [C_levelMap hs hM hnM] at hh
  have hna : n • levelMap s M hM A = levelMap s M hM (n • A) :=
    (map_nsmul (levelMap s M hM) n A).symm
  have hsa : s • levelMap s M hM A + levelMap s M hM B =
      levelMap s M hM (s • A + B) := by rw [map_add, map_nsmul]
  rw [hna, hsa, h_levelMap hs hM, h_levelMap hs hM] at hh
  exact hh

/-- The genuine modular Euclidean step, still retaining every larger-level defect. -/
theorem enlarged_modular_recurrence {M n s : ℕ} (hM : 0 < M) (hn : 0 < n) (hs : 0 < s)
    (hnM : n ∣ M) (τ : ℍ) (A B : Point M) :
    C M τ n s A B =
      (n : ℂ) * h M τ (n • A) * h M τ (s • A + B) -
      ((n : ℂ) / (s : ℂ)) * C (s * M) τ s (n % s)
        (levelMap s M hM A + rootPoint s M B) (-(n • rootPoint s M B)) +
      (1 / (s : ℂ)) * defectSum (s * M) τ n s (levelMap s M hM A) (rootPoint s M B) := by
  rw [enlarged_recurrence hM hn hs hnM τ A B]
  rw [slope_mod (dvd_mul_right s M) τ n]

/-- When the positive slope is less than the degree, the recursive degree
strictly decreases and the next slope lies in its proper range. -/
theorem euclidean_step {M n s : ℕ} (hM : 0 < M) (hn : 0 < n) (hs : 0 < s)
    (hsmall : s < n) (hnM : n ∣ M) (τ : ℍ) (A B : Point M) :
    C M τ n s A B =
      (n : ℂ) * h M τ (n • A) * h M τ (s • A + B) -
      ((n : ℂ) / (s : ℂ)) * C (s * M) τ s (n % s)
        (levelMap s M hM A + rootPoint s M B) (-(n • rootPoint s M B)) +
      (1 / (s : ℂ)) * defectSum (s * M) τ n s (levelMap s M hM A) (rootPoint s M B) ∧
      s < n ∧ n % s < s :=
  ⟨enlarged_modular_recurrence hM hn hs hnM τ A B, hsmall, Nat.mod_lt n hs⟩

/-- A terminating Euclidean expansion using only actual principal products
and explicit finite defect corrections. Every recursive ambient level is
recorded in the arguments; no correction is discarded or identified as Eisenstein. -/
def euclideanExpansion (n : ℕ) (_hn : 0 < n) (M : ℕ) (hM : 0 < M) (_hnM : n ∣ M)
    (τ : ℍ) (s : ℕ) (A B : Point M) : ℂ :=
  if hr : s % n = 0 then
    (n : ℂ) * h M τ (n • A) * h M τ B
  else
    let r := s % n
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    (n : ℂ) * h M τ (n • A) * h M τ (r • A + B) -
      ((n : ℂ) / (r : ℂ)) *
        euclideanExpansion r hrpos (r * M) (Nat.mul_pos hrpos hM) (dvd_mul_right r M) τ n
          (levelMap r M hM A + rootPoint r M B) (-(n • rootPoint r M B)) +
      (1 / (r : ℂ)) * defectSum (r * M) τ n r (levelMap r M hM A) (rootPoint r M B)
termination_by n
decreasing_by exact Nat.mod_lt s _hn

/-- The finite Euclidean expansion is exactly the actual correlation. -/
theorem euclideanExpansion_eq_C (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (hnM : n ∣ M)
    (τ : ℍ) (s : ℕ) (A B : Point M) :
    euclideanExpansion n hn M hM hnM τ s A B = C M τ n s A B := by
  induction n using Nat.strong_induction_on generalizing M s with
  | h n ih =>
    rw [euclideanExpansion]
    split_ifs with hr
    · have hh := slope_mod hnM τ s A B
      rw [hr] at hh
      exact (correlation_zero hM hn hnM τ A B).symm.trans hh.symm
    · dsimp only
      rw [ih (s % n) (Nat.mod_lt s hn)]
      exact (enlarged_recurrence hM hn (Nat.pos_of_ne_zero hr) hnM τ A B).symm.trans
        (slope_mod hnM τ s A B).symm

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelationEnlarge
