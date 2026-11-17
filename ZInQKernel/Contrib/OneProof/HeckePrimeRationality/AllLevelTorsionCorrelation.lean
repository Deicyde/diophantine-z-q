import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionNatRegular
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exact finite correlations of the actual zero-extended torsion function

The ambient torsion group has two residue coordinates. Every value is the
proved zero extension of the actual theta logarithmic derivative. The
quadratic defect is kept explicitly, with no Eisenstein or vanishing claim.
-/

noncomputable section

open Complex Set Function Finset
open scoped Real UpperHalfPlane BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelation

open TorsionDistributionTwo (reg reg_of_good reg_of_bad)

/-- The actual ambient level-M torsion label group, with τ-first coordinates. -/
abbrev Point (M : ℕ) := ZMod M × ZMod M

/-- The residue class of two integer labels. -/
def label (M : ℕ) (a b : ℤ) : Point M := ((a : ZMod M), (b : ZMod M))

lemma label_add (M : ℕ) (a b c d : ℤ) :
    label M a b + label M c d = label M (a + c) (b + d) := by
  apply Prod.ext <;> simp [label]

lemma label_neg (M : ℕ) (a b : ℤ) : -label M a b = label M (-a) (-b) := by
  apply Prod.ext <;> simp [label]

lemma label_nsmul (M n : ℕ) (a b : ℤ) :
    n • label M a b = label M ((n : ℤ) * a) ((n : ℤ) * b) := by
  apply Prod.ext <;> simp [label, nsmul_eq_mul]

lemma label_val {M : ℕ} (hM : 0 < M) (P : Point M) :
    label M (P.1.val : ℤ) (P.2.val : ℤ) = P := by
  have : NeZero M := ⟨hM.ne'⟩
  apply Prod.ext <;> simp [label]

lemma label_surjective {M : ℕ} (hM : 0 < M) (P : Point M) :
    ∃ a b : ℤ, label M a b = P := ⟨P.1.val, P.2.val, label_val hM P⟩

/-- The actual regularized torsion function evaluated on canonical labels. -/
def h (M : ℕ) (τ : ℍ) (P : Point M) : ℂ := reg M (P.1.val : ℤ) (P.2.val : ℤ) τ

/-- Representative independence follows from the proved actual shift law. -/
theorem reg_eq_of_label_eq {M : ℕ} (hM : 0 < M) (τ : ℍ) (a b c d : ℤ)
    (heq : label M a b = label M c d) : reg M a b τ = reg M c d τ := by
  have ha : (M : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a M).mp (congrArg Prod.fst heq).symm
  have hb : (M : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b M).mp (congrArg Prod.snd heq).symm
  obtain ⟨k, hk⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hka : a = c + (M : ℤ) * k := by linear_combination hk
  have hjb : b = d + (M : ℤ) * j := by linear_combination hj
  rw [hka, hjb, TorsionDistributionNat.reg_shift hM]

/-- Any integer representative evaluates to the actual zero extension. -/
theorem h_label {M : ℕ} (hM : 0 < M) (τ : ℍ) (a b : ℤ) :
    h M τ (label M a b) = reg M a b τ := by
  unfold h
  exact reg_eq_of_label_eq hM τ _ _ a b (label_val hM (label M a b))

lemma h_zero {M : ℕ} (hM : 0 < M) (τ : ℍ) : h M τ 0 = 0 := by
  rw [show (0 : Point M) = label M 0 0 by apply Prod.ext <;> simp [label], h_label hM]
  exact reg_of_bad ⟨dvd_zero _, dvd_zero _⟩ τ

/-- Oddness holds on all classes, including the zero class. -/
theorem h_neg {M : ℕ} (hM : 0 < M) (τ : ℍ) (P : Point M) :
    h M τ (-P) = -h M τ P := by
  obtain ⟨a, b, rfl⟩ := label_surjective hM P
  rw [label_neg, h_label hM, h_label hM]
  exact TorsionDistributionNat.reg_neg hM a b τ

lemma shiftedPoint_scale (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    Torsion.shiftedPoint (n * N) ((n : ℤ) * a) ((n : ℤ) * b) τ =
      Torsion.shiftedPoint N a b τ := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold Torsion.shiftedPoint
  push_cast
  field_simp [hnC, hNC]

lemma raw_scale (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    Torsion.torsionLogDerivative (n * N) ((n : ℤ) * a) ((n : ℤ) * b) τ =
      Torsion.torsionLogDerivative N a b τ := by
  unfold Torsion.torsionLogDerivative
  rw [shiftedPoint_scale n N hn hN]
  push_cast
  rw [mul_div_mul_left _ _ (show (n : ℂ) ≠ 0 by exact_mod_cast hn.ne')]

/-- Level scaling for the actual zero extension, without admissibility restrictions. -/
theorem reg_scale (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    reg (n * N) ((n : ℤ) * a) ((n : ℤ) * b) τ = reg N a b τ := by
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbad : (((n * N : ℕ) : ℤ) ∣ (n : ℤ) * a ∧
      ((n * N : ℕ) : ℤ) ∣ (n : ℤ) * b) ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
    push_cast
    rw [mul_dvd_mul_iff_left hnZ, mul_dvd_mul_iff_left hnZ]
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [reg_of_bad (hbad.mpr hg), reg_of_bad hg]
  · rw [reg_of_good (fun hb => hg (hbad.mp hb)), reg_of_good hg]
    exact raw_scale n N hn hN a b τ

/-- The finite index set enumerating E[n]. -/
abbrev DivisionIndex (n : ℕ) := Fin n × Fin n

/-- The standard embedding of E[n] into the ambient group when n divides M.
It represents the complex torsion point `(rτ+s)/n`. -/
def divisionPoint (M n : ℕ) (T : DivisionIndex n) : Point M :=
  label M (((M / n : ℕ) : ℤ) * (T.1.val : ℤ)) (((M / n : ℕ) : ℤ) * (T.2.val : ℤ))

/-- Actual degree-n distribution inside a single ambient level. -/
theorem distribution {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M)
    (τ : ℍ) (A : Point M) :
    (∑ T : DivisionIndex n, h M τ (A + divisionPoint M n T)) =
      (n : ℂ) * h M τ (n • A) := by
  obtain ⟨N, rfl⟩ := hnM
  have hN : 0 < N := Nat.pos_of_mul_pos_left hM
  obtain ⟨a, b, rfl⟩ := label_surjective hM A
  have hterm (T : DivisionIndex n) :
      h (n * N) τ (label (n * N) a b + divisionPoint (n * N) n T) =
      reg (n * N) (a + (N : ℤ) * (T.1.val : ℤ)) (b + (N : ℤ) * (T.2.val : ℤ)) τ := by
    simp only [divisionPoint, Nat.mul_div_cancel_left N hn, label_add]
    exact h_label hM τ _ _
  simp_rw [hterm]
  rw [Fintype.sum_prod_type' (fun r s : Fin n =>
    reg (n * N) (a + (N : ℤ) * (r.val : ℤ)) (b + (N : ℤ) * (s.val : ℤ)) τ)]
  rw [TorsionDistributionNat.reg_distribution_nat n N hn hN]
  rw [label_nsmul, h_label hM, reg_scale n N hn hN]

/-- The genuine n-torsion subgroup of the ambient residue group. -/
def torsionKernel (M n : ℕ) : AddSubgroup (Point M) where
  carrier := {P | n • P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change n • P = 0 at hP
    change n • Q = 0 at hQ
    change n • (P + Q) = 0
    rw [nsmul_add, hP, hQ, zero_add]
  neg_mem' := by
    intro P hP
    change n • P = 0 at hP
    change n • (-P) = 0
    rw [neg_nsmul, hP, neg_zero]

lemma point_finite {M : ℕ} (hM : 0 < M) : Finite (Point M) := by
  have : NeZero M := ⟨hM.ne'⟩
  infer_instance

lemma quotient_pos {M n : ℕ} (hM : 0 < M) (hnM : n ∣ M) : 0 < M / n := by
  have hp : 0 < n * (M / n) := by rw [Nat.mul_div_cancel' hnM]; exact hM
  exact Nat.pos_of_mul_pos_left hp

/-- Every enumerated point is killed by n. -/
theorem divisionPoint_torsion {M n : ℕ} (hnM : n ∣ M) (T : DivisionIndex n) :
    n • divisionPoint M n T = 0 := by
  have he : (n : ℤ) * ((M / n : ℕ) : ℤ) = (M : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hnM
  unfold divisionPoint
  rw [label_nsmul]
  simp only [← mul_assoc, he]
  apply Prod.ext <;> simp [label]

lemma scaled_residue_injective {M n : ℕ} (hM : 0 < M) (hnM : n ∣ M)
    {r t : Fin n}
    (heq : ((((M / n : ℕ) : ℤ) * (r.val : ℤ) : ℤ) : ZMod M) =
      ((((M / n : ℕ) : ℤ) * (t.val : ℤ) : ℤ) : ZMod M)) : r = t := by
  have hK : ((M / n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (quotient_pos hM hnM).ne'
  have he : (M : ℤ) = ((M / n : ℕ) : ℤ) * (n : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hnM).symm.trans (Nat.mul_comm n (M / n))
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (((M / n : ℕ) : ℤ) * (r.val : ℤ)) (((M / n : ℕ) : ℤ) * (t.val : ℤ)) M).mp heq
  rw [he, show ((M / n : ℕ) : ℤ) * (t.val : ℤ) - ((M / n : ℕ) : ℤ) * (r.val : ℤ) =
    ((M / n : ℕ) : ℤ) * ((t.val : ℤ) - (r.val : ℤ)) by ring] at hd
  have hdiff : (n : ℤ) ∣ (t.val : ℤ) - (r.val : ℤ) := (mul_dvd_mul_iff_left hK).mp hd
  have hz := (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val : ℤ) (t.val : ℤ) n).mpr hdiff
  have hv := congrArg (fun x : ZMod n => x.val) hz
  simp only [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt r.is_lt,
    Nat.mod_eq_of_lt t.is_lt] at hv
  exact Fin.ext hv

/-- The index set has no repeated ambient torsion classes. -/
theorem divisionPoint_injective {M n : ℕ} (hM : 0 < M) (hnM : n ∣ M) :
    Function.Injective (divisionPoint M n) := by
  intro T U heq
  apply Prod.ext
  · exact scaled_residue_injective hM hnM (congrArg Prod.fst heq)
  · exact scaled_residue_injective hM hnM (congrArg Prod.snd heq)

/-- The index set exhausts the actual n-torsion subgroup. -/
theorem torsion_iff_divisionPoint {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M)
    (P : Point M) : n • P = 0 ↔ ∃ T : DivisionIndex n, divisionPoint M n T = P := by
  constructor
  · intro hp
    have : NeZero M := ⟨hM.ne'⟩
    let a : ℤ := P.1.val
    let b : ℤ := P.2.val
    let K : ℤ := (M / n : ℕ)
    have hK : 0 < K := by
      dsimp [K]
      exact_mod_cast quotient_pos hM hnM
    have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : (M : ℤ) = (n : ℤ) * K := by
      dsimp [K]
      exact_mod_cast (Nat.mul_div_cancel' hnM).symm
    have ha0 : 0 ≤ a := Int.natCast_nonneg _
    have hb0 : 0 ≤ b := Int.natCast_nonneg _
    have haM : a < (M : ℤ) := by
      dsimp [a]
      exact_mod_cast ZMod.val_lt P.1
    have hbM : b < (M : ℤ) := by
      dsimp [b]
      exact_mod_cast ZMod.val_lt P.2
    have hval : label M a b = P := label_val hM P
    have hzero : label M ((n : ℤ) * a) ((n : ℤ) * b) = 0 := by
      rw [← label_nsmul, hval, hp]
    have hna : (M : ℤ) ∣ (n : ℤ) * a :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp (congrArg Prod.fst hzero)
    have hnb : (M : ℤ) ∣ (n : ℤ) * b :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp (congrArg Prod.snd hzero)
    rw [he] at hna hnb
    obtain ⟨r, har⟩ := (mul_dvd_mul_iff_left hnZ).mp hna
    obtain ⟨t, hbt⟩ := (mul_dvd_mul_iff_left hnZ).mp hnb
    have hr0 : 0 ≤ r := by nlinarith
    have ht0 : 0 ≤ t := by nlinarith
    have hrn : r < (n : ℤ) := by rw [he] at haM; nlinarith
    have htn : t < (n : ℤ) := by rw [he] at hbM; nlinarith
    let R : Fin n := ⟨r.toNat, by omega⟩
    let S : Fin n := ⟨t.toNat, by omega⟩
    refine ⟨(R, S), ?_⟩
    unfold divisionPoint
    simp only [R, S, Int.toNat_of_nonneg hr0, Int.toNat_of_nonneg ht0]
    change label M (K * r) (K * t) = P
    rw [← har, ← hbt]
    exact hval
  · rintro ⟨T, rfl⟩
    exact divisionPoint_torsion hnM T

/-- Identification of the n² indices with the genuine finite torsion group. -/
def divisionEquiv {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M) :
    DivisionIndex n ≃ torsionKernel M n :=
  Equiv.ofBijective (fun T => ⟨divisionPoint M n T, divisionPoint_torsion hnM T⟩)
    ⟨fun T U heq => divisionPoint_injective hM hnM (congrArg Subtype.val heq),
      fun P => by
        obtain ⟨T, hT⟩ := (torsion_iff_divisionPoint hM hn hnM P.1).mp P.2
        exact ⟨T, Subtype.ext hT⟩⟩

/-- The explicit quadratic defect of the actual regularized function. -/
def D (M : ℕ) (τ : ℍ) (P Q : Point M) : ℂ :=
  h M τ P * h M τ Q - h M τ P * h M τ (P + Q) - h M τ Q * h M τ (P + Q)

/-- The actual finite correlation over the embedded n-torsion points. -/
def C (M : ℕ) (τ : ℍ) (n s : ℕ) (A B : Point M) : ℂ :=
  ∑ T : DivisionIndex n,
    h M τ (A + divisionPoint M n T) * h M τ (B - s • divisionPoint M n T)

/-- The correction is retained as an actual finite sum, not declared zero. -/
def defectSum (M : ℕ) (τ : ℍ) (n s : ℕ) (A B' : Point M) : ℂ :=
  ∑ T : DivisionIndex n, ∑ U : DivisionIndex s,
    D M τ (A + divisionPoint M n T) (B' - divisionPoint M n T + divisionPoint M s U)

lemma D_zero_left {M : ℕ} (hM : 0 < M) (τ : ℍ) (Q : Point M) :
    D M τ 0 Q = -(h M τ Q) ^ 2 := by
  simp [D, h_zero hM, pow_two]

lemma D_zero_right {M : ℕ} (hM : 0 < M) (τ : ℍ) (P : Point M) :
    D M τ P 0 = -(h M τ P) ^ 2 := by
  simp [D, h_zero hM, pow_two]

lemma D_neg {M : ℕ} (hM : 0 < M) (τ : ℍ) (P : Point M) :
    D M τ P (-P) = -(h M τ P) ^ 2 := by
  simp [D, h_zero hM, h_neg hM, pow_two]

/-- The zero-slope base case uses proved actual all-label distribution. -/
theorem correlation_zero {M n : ℕ} (hM : 0 < M) (hn : 0 < n) (hnM : n ∣ M)
    (τ : ℍ) (A B : Point M) :
    C M τ n 0 A B = (n : ℂ) * h M τ (n • A) * h M τ B := by
  unfold C
  simp only [zero_nsmul, sub_zero]
  rw [← Finset.sum_mul, distribution hM hn hnM]

/-- Exact finite-correlation recurrence. Both torsion kernels lie in the
ambient level; the displayed preimage relation is an equality of classes.
The defect correction includes all degenerate classes. -/
theorem correlation_recurrence {M n s : ℕ}
    (hM : 0 < M) (hn : 0 < n) (hs : 0 < s) (hnM : n ∣ M) (hsM : s ∣ M)
    (τ : ℍ) (A B B' : Point M) (hB : s • B' = B) :
    C M τ n s A B =
      (n : ℂ) * h M τ (n • A) * h M τ (s • A + B) -
      ((n : ℂ) / (s : ℂ)) * C M τ s n (A + B') (-(n • B')) +
      (1 / (s : ℂ)) * defectSum M τ n s A B' := by
  let X : DivisionIndex n → Point M := divisionPoint M n
  let Y : DivisionIndex s → Point M := divisionPoint M s
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hdist (T : DivisionIndex n) :
      (∑ U : DivisionIndex s, h M τ (B' - X T + Y U)) =
        (s : ℂ) * h M τ (B - s • X T) := by
    have hh := distribution hM hs hsM τ (B' - X T)
    simpa only [nsmul_sub, hB] using hh
  have hstart : C M τ n s A B =
      (1 / (s : ℂ)) * ∑ T : DivisionIndex n, ∑ U : DivisionIndex s,
        h M τ (A + X T) * h M τ (B' - X T + Y U) := by
    unfold C
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [← Finset.mul_sum, hdist T]
    dsimp [X]
    field_simp [hsC]
  have hterm (T : DivisionIndex n) (U : DivisionIndex s) :
      h M τ (A + X T) * h M τ (B' - X T + Y U) =
        h M τ (A + X T) * h M τ (A + B' + Y U) -
        h M τ (-B' + X T - Y U) * h M τ (A + B' + Y U) +
        D M τ (A + X T) (B' - X T + Y U) := by
    have hsum : (A + X T) + (B' - X T + Y U) = A + B' + Y U := by abel
    have hneg : h M τ (B' - X T + Y U) = -h M τ (-B' + X T - Y U) := by
      rw [show -B' + X T - Y U = -(B' - X T + Y U) by abel, h_neg hM, neg_neg]
    have hh : h M τ (A + X T) * h M τ (B' - X T + Y U) =
        h M τ (A + X T) * h M τ (A + B' + Y U) +
        h M τ (B' - X T + Y U) * h M τ (A + B' + Y U) +
        D M τ (A + X T) (B' - X T + Y U) := by
      unfold D
      rw [hsum]
      ring
    rw [hh, hneg]
    ring
  have hfirst : (∑ T : DivisionIndex n, ∑ U : DivisionIndex s,
      h M τ (A + X T) * h M τ (A + B' + Y U)) =
      (n : ℂ) * (s : ℂ) * h M τ (n • A) * h M τ (s • A + B) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, distribution hM hn hnM, distribution hM hs hsM,
      nsmul_add, hB]
    ring
  have hsecond : (∑ T : DivisionIndex n, ∑ U : DivisionIndex s,
      h M τ (-B' + X T - Y U) * h M τ (A + B' + Y U)) =
      (n : ℂ) * C M τ s n (A + B') (-(n • B')) := by
    rw [Finset.sum_comm]
    have hinner (U : DivisionIndex s) :
        (∑ T : DivisionIndex n, h M τ (-B' + X T - Y U)) =
          (n : ℂ) * h M τ (-(n • B') - n • Y U) := by
      simp_rw [show ∀ T : DivisionIndex n, -B' + X T - Y U = (-B' - Y U) + X T
        from fun T => by abel]
      have hh := distribution hM hn hnM τ (-B' - Y U)
      simpa only [nsmul_sub, neg_nsmul] using hh
    simp_rw [← Finset.sum_mul, hinner]
    unfold C
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    dsimp [Y]
    ring
  have hwhole : (∑ T : DivisionIndex n, ∑ U : DivisionIndex s,
      h M τ (A + X T) * h M τ (B' - X T + Y U)) =
      (n : ℂ) * (s : ℂ) * h M τ (n • A) * h M τ (s • A + B) -
        (n : ℂ) * C M τ s n (A + B') (-(n • B')) + defectSum M τ n s A B' := by
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hfirst, hsecond]
    rfl
  rw [hstart, hwhole]
  field_simp [hsC]

end ZInQ.Contrib.HeckePrimeRationality.TorsionCorrelation
