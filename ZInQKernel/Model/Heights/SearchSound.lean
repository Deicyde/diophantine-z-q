import ZInQKernel.Model.Heights.SearchCheck
import ZInQKernel.Model.Heights.SquareTest

/-!
# Soundness of the checker for the small-height search

Blueprint: `model/heights/small-height-search.md`.

* `possSq_of_isSquare`: if `u + v s` is a square in `K₀` (`u, v ∈ ℤ`), then `possSq u v = true`.
* `mem_qList_iff`: `(a, i, K) ∈ qList` iff `a ∈ [1, 81]`, `b' = i - 81 ∈ [-81, 81]`,
  `K ∈ [1, 81]`, and `c = (b'² - 2K²)/a` is an integer with `|c| ≤ 81` and `gcd(a, 2b', c) = 1`;
  `qList` has no duplicates.
-/

namespace ZInQ.Search

open ZInQ


theorem fastSqrt_mul_self (W : ℤ) : (fastSqrt (W * W).toNat : ℤ) = |W| := by
  rw [fastSqrt_eq]
  have : (W * W).toNat = W.natAbs * W.natAbs := by
    have : ((W * W).toNat : ℤ) = ((W.natAbs * W.natAbs : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (mul_self_nonneg W)]; push_cast; rw [abs_mul_abs_self]
    exact_mod_cast this
  rw [this, Nat.sqrt_eq, Int.natCast_natAbs]

/-- If an integer is the square of a rational, it is the square `W * W` of an integer. -/
theorem exists_int_of_rat_sq {n : ℤ} {q : ℚ} (h : (n : ℚ) = q ^ 2) : ∃ W : ℤ, n = W * W := by
  have : IsSquare (n : ℚ) := ⟨q, by rw [h, pow_two]⟩
  exact Rat.isSquare_intCast_iff.mp this

theorem isSqNat_of_rat_sq {n : ℤ} {q : ℚ} (h : (n : ℚ) = q ^ 2) : isSqNat n.toNat = true := by
  obtain ⟨W, rfl⟩ := exists_int_of_rat_sq h
  unfold isSqNat
  rw [Nat.beq_eq]
  have h1 := fastSqrt_mul_self W
  have h2 : ((W * W).toNat : ℤ) = W * W := Int.toNat_of_nonneg (mul_self_nonneg W)
  have : ((fastSqrt (W * W).toNat * fastSqrt (W * W).toNat : ℕ) : ℤ) = ((W * W).toNat : ℤ) := by
    push_cast; rw [h1, h2, abs_mul_abs_self]
  exact_mod_cast this

/-- `okBranch u m = true` when `m = 2 y₀²` and `u = y₀² + 2 y₁²` (rationals `y₀, y₁`). -/
theorem okBranch_of {u m : ℤ} {y₀ y₁ : ℚ} (hm : (m : ℚ) = 2 * y₀ ^ 2)
    (hu : (u : ℚ) = y₀ ^ 2 + 2 * y₁ ^ 2) : okBranch u m = true := by
  have h2m : ((2 * m : ℤ) : ℚ) = (2 * y₀) ^ 2 := by push_cast; rw [hm]; ring
  obtain ⟨Y, hY⟩ := exists_int_of_rat_sq h2m
  have hm0 : 0 ≤ m := by
    have : (0 : ℚ) ≤ m := by rw [hm]; positivity
    exact_mod_cast this
  unfold okBranch
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Nat.beq_eq]
  refine ⟨hm0, ?_⟩
  rw [hY]
  have h1 := fastSqrt_mul_self Y
  have h2 : ((Y * Y).toNat : ℤ) = Y * Y := Int.toNat_of_nonneg (mul_self_nonneg Y)
  refine ⟨?_, ?_⟩
  · have : ((fastSqrt (Y * Y).toNat * fastSqrt (Y * Y).toNat : ℕ) : ℤ) = ((Y * Y).toNat : ℤ) := by
      push_cast; rw [h1, h2, abs_mul_abs_self]
    exact_mod_cast this
  · by_cases hY0 : Y = 0
    · right
      have hy0 : y₀ = 0 := by
        have : ((Y * Y : ℤ) : ℚ) = (2 * y₀) ^ 2 := by rw [← hY]; exact h2m
        rw [hY0] at this; push_cast at this
        have : (2 * y₀) ^ 2 = 0 := this.symm
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        linarith
      rw [hy0] at hu
      refine ⟨?_, isSqNat_of_rat_sq (q := 2 * y₁) (by push_cast; rw [hu]; ring)⟩
      have : (0 : ℚ) ≤ u := by rw [hu]; positivity
      exact_mod_cast this
    · left
      rw [← Bool.not_eq_true, Nat.beq_eq]
      intro h
      have : (fastSqrt (Y * Y).toNat : ℤ) = 0 := by exact_mod_cast h
      rw [h1, abs_eq_zero] at this
      exact hY0 this

/-- **Soundness of the square test**: if `u + v s` is a square in `K₀` then `possSq u v`. -/
theorem possSq_of_isSquare {u v : ℤ} (h : IsSquare (⟨(u : ℚ), (v : ℚ)⟩ : K0)) :
    possSq u v = true := by
  obtain ⟨r, hr⟩ := h
  have hr' : (⟨(u : ℚ), (v : ℚ)⟩ : K0) = ⟨r.re, r.im⟩ ^ 2 := by rw [hr, pow_two]
  rw [pow_two, K0.mk_mul_mk'] at hr'
  have hu : (u : ℚ) = r.re ^ 2 + 2 * r.im ^ 2 := by
    have := congrArg QuadraticAlgebra.re hr'; simp at this; rw [this]; ring
  have hv : (v : ℚ) = 2 * r.re * r.im := by
    have := congrArg QuadraticAlgebra.im hr'; simp at this; rw [this]; ring
  set y₀ := r.re
  set y₁ := r.im
  have hN : ((u * u - 2 * v * v : ℤ) : ℚ) = (y₀ ^ 2 - 2 * y₁ ^ 2) ^ 2 := by
    push_cast; rw [hu, hv]; ring
  obtain ⟨W, hW⟩ := exists_int_of_rat_sq hN
  have hWq : ((W : ℚ)) ^ 2 = (y₀ ^ 2 - 2 * y₁ ^ 2) ^ 2 := by
    rw [← hN, hW]; push_cast; ring
  unfold possSq
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  rw [hW, fastSqrt_mul_self W]
  refine ⟨mul_self_nonneg W, abs_mul_abs_self W, ?_⟩
  -- `W = ± (y₀² - 2 y₁²)`
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hWq with hw | hw
  · -- `W = y₀² - 2y₁²`
    rcases le_or_gt 0 W with h0 | h0
    · left; rw [abs_of_nonneg h0]
      exact okBranch_of (y₀ := y₀) (y₁ := y₁) (by push_cast; rw [hw, hu]; ring) hu
    · right; rw [abs_of_neg h0]
      exact okBranch_of (y₀ := y₀) (y₁ := y₁) (by push_cast; rw [hw, hu]; ring) hu
  · rcases le_or_gt 0 W with h0 | h0
    · right; rw [abs_of_nonneg h0]
      exact okBranch_of (y₀ := y₀) (y₁ := y₁) (by push_cast; rw [hw, hu]; ring) hu
    · left; rw [abs_of_neg h0]
      exact okBranch_of (y₀ := y₀) (y₁ := y₁) (by push_cast; rw [hw, hu]; ring) hu


theorem aLoop_zero (B m lo : ℕ) : aLoop B m lo 0 = [] := rfl
theorem aLoop_succ (B m lo n : ℕ) :
    aLoop B m lo (n + 1) = bif aCond B m (lo + n) then (lo + n) :: aLoop B m lo n
      else aLoop B m lo n := rfl

theorem mem_aLoop {B m lo cnt a : ℕ} :
    a ∈ aLoop B m lo cnt ↔ lo ≤ a ∧ a < lo + cnt ∧ aCond B m a = true := by
  induction cnt with
  | zero => simp [aLoop_zero]; omega
  | succ n ih =>
    rw [aLoop_succ]
    cases h : aCond B m (lo + n)
    · simp only [Bool.cond_false, ih]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        rcases Nat.lt_or_ge a (lo + n) with h4 | h4
        · exact h4
        · have : a = lo + n := by omega
          rw [this, h] at h3; exact absurd h3 (by simp)
    · simp only [Bool.cond_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨by omega, by omega, h⟩
        · exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.lt_or_ge a (lo + n) with h4 | h4
        · exact Or.inr ⟨h1, h4, h3⟩
        · exact Or.inl (by omega)

theorem aLoop_nodup (B m lo cnt : ℕ) : (aLoop B m lo cnt).Nodup := by
  induction cnt with
  | zero => simp [aLoop_zero]
  | succ n ih =>
    rw [aLoop_succ]
    cases aCond B m (lo + n)
    · exact ih
    · simp only [Bool.cond_true, List.nodup_cons, mem_aLoop]
      exact ⟨by omega, ih⟩

theorem kLoop_zero (i : ℕ) : kLoop i 0 = [] := rfl
theorem kLoop_succ (i n : ℕ) :
    kLoop i (n + 1) = (cands i (n + 1)).map (fun a => (a, i, n + 1)) ++ kLoop i n := rfl

theorem mem_kLoop {i cnt : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ kLoop i cnt ↔ t.2.1 = i ∧ 1 ≤ t.2.2 ∧ t.2.2 ≤ cnt ∧ t.1 ∈ cands i t.2.2 := by
  obtain ⟨a, j, K⟩ := t
  induction cnt with
  | zero => simp [kLoop_zero]; omega
  | succ n ih =>
    rw [kLoop_succ, List.mem_append, ih, List.mem_map]
    simp only [Prod.mk.injEq]
    constructor
    · rintro (⟨a', ha', rfl, rfl, rfl⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨rfl, by omega, le_refl _, ha'⟩
      · exact ⟨h1, h2, by omega, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      rcases Nat.lt_or_ge K (n + 1) with h5 | h5
      · exact Or.inr ⟨h1, h2, by omega, h4⟩
      · have : K = n + 1 := by omega
        subst this
        exact Or.inl ⟨a, h4, rfl, h1.symm, rfl⟩

theorem kLoop_nodup (i cnt : ℕ) : (kLoop i cnt).Nodup := by
  induction cnt with
  | zero => simp [kLoop_zero]
  | succ n ih =>
    rw [kLoop_succ, List.nodup_append]
    refine ⟨(aLoop_nodup _ _ _ _).map (fun a b h => by simpa using h), ih, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rw [mem_kLoop] at hy
    subst hxy
    simp at hy

theorem iLoop_zero : iLoop 0 = [] := rfl
theorem iLoop_succ (n : ℕ) : iLoop (n + 1) = kLoop n 81 ++ iLoop n := rfl

theorem mem_iLoop {cnt : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ iLoop cnt ↔ t.2.1 < cnt ∧ t ∈ kLoop t.2.1 81 := by
  induction cnt with
  | zero => simp [iLoop_zero]
  | succ n ih =>
    rw [iLoop_succ, List.mem_append, ih]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · have := (mem_kLoop.mp h).1
        rw [this]; exact ⟨by omega, h⟩
      · exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge t.2.1 n with h3 | h3
      · exact Or.inr ⟨h3, h2⟩
      · have : t.2.1 = n := by omega
        rw [this] at h2; exact Or.inl h2

theorem iLoop_nodup (cnt : ℕ) : (iLoop cnt).Nodup := by
  induction cnt with
  | zero => simp [iLoop_zero]
  | succ n ih =>
    rw [iLoop_succ, List.nodup_append]
    refine ⟨kLoop_nodup _ _, ih, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have h1 := (mem_kLoop.mp hx).1
    have h2 := (mem_iLoop.mp hy).1
    omega

theorem qList_nodup : qList.Nodup := iLoop_nodup 163

/-- Membership in `qList`. -/
theorem mem_qList {a i K : ℕ} :
    (a, i, K) ∈ qList ↔ i < 163 ∧ 1 ≤ K ∧ K ≤ 81 ∧ loOf (mOf (absB i) K) ≤ a ∧ a < 82 ∧
      aCond (absB i) (mOf (absB i) K) a = true := by
  rw [qList, mem_iLoop, mem_kLoop]
  simp only [cands, mem_aLoop]
  constructor
  · rintro ⟨h1, -, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, by omega, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, trivial, h2, h3, h4, by omega, h6⟩


theorem absB_eq (i : ℕ) : (absB i : ℤ) = |(i : ℤ) - 81| := by
  unfold absB
  cases h : Nat.ble 81 i
  · simp only [Bool.cond_false]
    have : ¬ 81 ≤ i := fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; exact absurd h (by simp)
    rw [abs_of_neg (by omega)]; push_cast [show i ≤ 81 by omega]; ring
  · simp only [Bool.cond_true]
    have : 81 ≤ i := by simpa using h
    rw [abs_of_nonneg (by omega)]; push_cast [this]; ring

theorem absB_natAbs (i : ℕ) : absB i = ((i : ℤ) - 81).natAbs := by
  have := absB_eq i
  rw [← Int.natCast_natAbs] at this
  exact_mod_cast this

theorem mOf_eq (B K : ℕ) : mOf B K = ((B : ℤ) ^ 2 - 2 * (K : ℤ) ^ 2).natAbs := by
  unfold mOf
  cases h : Nat.ble (2 * K * K) (B * B)
  · simp only [Bool.cond_false]
    have h' : ¬ 2 * K * K ≤ B * B := fun h' => by
      rw [Nat.ble_eq_true_of_le h'] at h; exact absurd h (by simp)
    replace h' : B * B < 2 * K * K := by omega
    have : ((B : ℤ) ^ 2 - 2 * (K : ℤ) ^ 2) = -((2 * K * K - B * B : ℕ) : ℤ) := by
      push_cast [h'.le]; ring
    rw [this, Int.natAbs_neg, Int.natAbs_natCast]
  · simp only [Bool.cond_true]
    have h' : 2 * K * K ≤ B * B := by simpa using h
    have : ((B : ℤ) ^ 2 - 2 * (K : ℤ) ^ 2) = ((B * B - 2 * K * K : ℕ) : ℤ) := by
      push_cast [h']; ring
    rw [this, Int.natAbs_natCast]

theorem mOf_absB (i K : ℕ) :
    mOf (absB i) K = (((i : ℤ) - 81) ^ 2 - 2 * (K : ℤ) ^ 2).natAbs := by
  rw [mOf_eq, absB_eq, sq_abs]

/-- Membership in `qList`, in terms of integers: `a ∈ [1, 81]`, `b' = i - 81 ∈ [-81, 81]`,
`K ∈ [1, 81]`, and `c = (b'² - 2K²)/a` an integer with `|c| ≤ 81` and `gcd(a, 2b', c) = 1`. -/
theorem mem_qList_iff {a i K : ℕ} :
    (a, i, K) ∈ qList ↔ 1 ≤ a ∧ a ≤ 81 ∧ i ≤ 162 ∧ 1 ≤ K ∧ K ≤ 81 ∧
      ∃ c : ℤ, c * a = ((i : ℤ) - 81) ^ 2 - 2 * (K : ℤ) ^ 2 ∧ |c| ≤ 81 ∧
        Int.gcd (Int.gcd a (2 * ((i : ℤ) - 81))) c = 1 := by
  rw [mem_qList, mOf_absB, absB_natAbs]
  set n : ℤ := ((i : ℤ) - 81) ^ 2 - 2 * (K : ℤ) ^ 2
  set B : ℕ := ((i : ℤ) - 81).natAbs
  have h2B : (2 * ((i : ℤ) - 81)).natAbs = 2 * B := by
    rw [Int.natAbs_mul]; rfl
  unfold aCond loOf
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]
  constructor
  · rintro ⟨hi, hK1, hK2, hlo, ha, ⟨hmod, hle⟩, hgcd⟩
    have ha1 : 1 ≤ a := le_trans (Nat.le_max_right _ _) hlo
    have hdvd : (a : ℤ) ∣ n := Int.natCast_dvd.mpr (Nat.dvd_of_mod_eq_zero hmod)
    obtain ⟨c, hc⟩ := hdvd
    have hcn : n.natAbs = c.natAbs * a := by
      rw [hc, Int.natAbs_mul, Int.natAbs_natCast, mul_comm]
    have hdiv : n.natAbs / a = c.natAbs := by
      rw [hcn, Nat.mul_div_cancel _ (by omega)]
    refine ⟨ha1, by omega, by omega, hK1, hK2, c, by rw [hc]; ring, ?_, ?_⟩
    · have : c.natAbs ≤ 81 := by
        rw [hcn] at hle
        exact Nat.le_of_mul_le_mul_right hle (by omega : 0 < a)
      rw [Int.abs_eq_natAbs]; exact_mod_cast this
    · rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, Int.gcd_eq_natAbs_gcd_natAbs,
        Int.natAbs_natCast, h2B, ← hdiv]
      exact hgcd
  · rintro ⟨ha1, ha2, hi, hK1, hK2, c, hc, habs, hgcd⟩
    have hcn : n.natAbs = c.natAbs * a := by
      rw [← hc, Int.natAbs_mul, Int.natAbs_natCast]
    have hc81 : c.natAbs ≤ 81 := by
      rw [Int.abs_eq_natAbs] at habs; exact_mod_cast habs
    have hdiv : n.natAbs / a = c.natAbs := by
      rw [hcn, Nat.mul_div_cancel _ (by omega)]
    refine ⟨by omega, hK1, hK2, ?_, by omega, ⟨?_, ?_⟩, ?_⟩
    · apply max_le _ ha1
      rw [hcn]
      have : c.natAbs * a ≤ 81 * a := Nat.mul_le_mul_right _ hc81
      omega
    · rw [hcn]; simp
    · rw [hcn]; exact Nat.mul_le_mul_right _ hc81
    · rw [hdiv]
      rwa [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, Int.gcd_eq_natAbs_gcd_natAbs,
        Int.natAbs_natCast, h2B] at hgcd

end ZInQ.Search
