import ZInQKernel.Model.Heights.DuplicationBounds

/-!
# The canonical height on `C(K₀)`

Blueprint: `model/heights/canonical-height.md`, `model/heights/canonical-height-bounds.md`,
`model/heights/canonical-height-quadratic.md`.

`ĥ(T) = ½ lim_{m → ∞} 4^{-m} h_x([2^m] T)`. The duplication height bounds make the sequence
Cauchy, with `-log 392 / 3 ≤ lim - h_x(T) ≤ log 676 / 3`. Mathlib's approximate parallelogram law
for the naive height (`= 2 h_x`) gives the exact parallelogram law for `ĥ` in the limit, hence
`ĥ([m] P) = m² ĥ(P)`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine Filter Topology

/-- The sequence `4^{-m} h_x([2^m] T)`. -/
noncomputable def hxSeq (T : curveC.toAffine.Point) (m : ℕ) : ℝ := hx ((2 ^ m) • T) / 4 ^ m

/-- The canonical height `ĥ(T) = ½ lim_m 4^{-m} h_x([2^m] T)`. -/
noncomputable def canonHeight (T : curveC.toAffine.Point) : ℝ :=
  (limUnder atTop fun m : ℕ => hx ((2 ^ m) • T) / 4 ^ m) / 2

theorem canonHeight_eq (T : curveC.toAffine.Point) :
    canonHeight T = limUnder atTop (hxSeq T) / 2 := rfl

theorem two_pow_succ_smul (T : curveC.toAffine.Point) (m : ℕ) :
    (2 ^ (m + 1)) • T = 2 • ((2 ^ m) • T) := by
  rw [smul_smul, pow_succ']

theorem hxSeq_zero (T : curveC.toAffine.Point) : hxSeq T 0 = hx T := by
  simp [hxSeq]

/-- `c_m - 4^{-m-1} log 392 ≤ c_{m+1} ≤ c_m + 4^{-m-1} log 676`. -/
theorem hxSeq_succ_bounds (T : curveC.toAffine.Point) (m : ℕ) :
    hxSeq T m - Real.log 392 / 4 ^ (m + 1) ≤ hxSeq T (m + 1) ∧
      hxSeq T (m + 1) ≤ hxSeq T m + Real.log 676 / 4 ^ (m + 1) := by
  obtain ⟨h1, h2⟩ := hx_two_smul_bounds ((2 ^ m) • T)
  have h4 : (0 : ℝ) < 4 ^ (m + 1) := by positivity
  have e : hxSeq T m = 4 * hx ((2 ^ m) • T) / 4 ^ (m + 1) := by
    rw [hxSeq, pow_succ]; field_simp
  have hs : hxSeq T (m + 1) = hx (2 • ((2 ^ m) • T)) / 4 ^ (m + 1) := by
    rw [hxSeq, two_pow_succ_smul]
  rw [hs, e]
  constructor
  · rw [← sub_div]; exact div_le_div_of_nonneg_right h1 h4.le
  · rw [← add_div]; exact div_le_div_of_nonneg_right h2 h4.le

theorem log_392_le_log_676 : Real.log 392 ≤ Real.log 676 :=
  Real.log_le_log (by norm_num) (by norm_num)

theorem hxSeq_cauchy (T : curveC.toAffine.Point) : CauchySeq (hxSeq T) := by
  refine cauchySeq_of_le_geometric (1 / 4) (Real.log 676 / 4) (by norm_num) fun n => ?_
  obtain ⟨h1, h2⟩ := hxSeq_succ_bounds T n
  have := log_392_le_log_676
  have e : Real.log 676 / 4 * (1 / 4) ^ n = Real.log 676 / 4 ^ (n + 1) := by
    rw [one_div_pow, pow_succ]; field_simp
  have e' : Real.log 392 / 4 ^ (n + 1) ≤ Real.log 676 / 4 ^ (n + 1) :=
    div_le_div_of_nonneg_right this (by positivity)
  rw [Real.dist_eq, e, abs_le]
  constructor <;> linarith

/-- **The limit defining `ĥ(T)` exists.** -/
theorem canonHeight_tendsto (T : curveC.toAffine.Point) :
    Tendsto (fun m : ℕ => hx ((2 ^ m) • T) / 4 ^ m) atTop (𝓝 (2 * canonHeight T)) := by
  have h := tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hxSeq_cauchy T))
  rw [canonHeight_eq, mul_div_cancel₀ _ two_ne_zero]
  exact h

theorem hxSeq_tendsto (T : curveC.toAffine.Point) :
    Tendsto (hxSeq T) atTop (𝓝 (2 * canonHeight T)) := canonHeight_tendsto T

/-- The partial sums of the geometric bounds. -/
theorem hxSeq_bounds_aux (T : curveC.toAffine.Point) (m : ℕ) :
    hx T - Real.log 392 / 3 * (1 - (1 / 4) ^ m) ≤ hxSeq T m ∧
      hxSeq T m ≤ hx T + Real.log 676 / 3 * (1 - (1 / 4) ^ m) := by
  induction m with
  | zero => simp [hxSeq_zero]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := hxSeq_succ_bounds T m
    have e : ∀ c : ℝ, c / 4 ^ (m + 1) = c / 4 * (1 / 4) ^ m := by
      intro c; rw [one_div_pow, pow_succ]; field_simp
    rw [e] at h1 h2
    have e2 : ∀ c : ℝ, c / 3 * (1 - (1 / 4) ^ (m + 1)) = c / 3 * (1 - (1 / 4) ^ m) + c / 4 * (1 / 4) ^ m := by
      intro c; rw [pow_succ]; ring
    rw [e2, e2]
    constructor <;> linarith [ih.1, ih.2]

theorem hxSeq_bounds (T : curveC.toAffine.Point) (m : ℕ) :
    hx T - Real.log 392 / 3 ≤ hxSeq T m ∧ hxSeq T m ≤ hx T + Real.log 676 / 3 := by
  obtain ⟨h1, h2⟩ := hxSeq_bounds_aux T m
  have hq : 0 ≤ (1 / 4 : ℝ) ^ m := by positivity
  have h392 : 0 ≤ Real.log 392 := Real.log_nonneg (by norm_num)
  have h676 : 0 ≤ Real.log 676 := Real.log_nonneg (by norm_num)
  constructor <;> nlinarith

/-- **Basic properties (1).** `2 ĥ(T) ≤ h_x(T) + log 676 / 3`. -/
theorem two_canonHeight_le (T : curveC.toAffine.Point) :
    2 * canonHeight T ≤ hx T + Real.log 676 / 3 :=
  le_of_tendsto' (hxSeq_tendsto T) fun m => (hxSeq_bounds T m).2

/-- **Basic properties (1).** `h_x(T) ≤ 2 ĥ(T) + log 392 / 3`. -/
theorem hx_le_two_canonHeight (T : curveC.toAffine.Point) :
    hx T ≤ 2 * canonHeight T + Real.log 392 / 3 := by
  have := ge_of_tendsto' (hxSeq_tendsto T) fun m => (hxSeq_bounds T m).1
  linarith

/-- **Basic properties (2).** `ĥ([2]T) = 4 ĥ(T)`. -/
theorem canonHeight_two_smul (T : curveC.toAffine.Point) :
    canonHeight (2 • T) = 4 * canonHeight T := by
  have h1 := hxSeq_tendsto (2 • T)
  have h2 : Tendsto (fun m => 4 * hxSeq T (m + 1)) atTop (𝓝 (4 * (2 * canonHeight T))) :=
    ((hxSeq_tendsto T).comp (tendsto_add_atTop_nat 1)).const_mul 4
  have e : hxSeq (2 • T) = fun m => 4 * hxSeq T (m + 1) := by
    funext m
    rw [hxSeq, hxSeq, smul_smul, ← pow_succ]
    field_simp
    ring
  rw [e] at h1
  have := tendsto_nhds_unique h1 h2
  linarith

/-- **Basic properties (3).** `ĥ(-T) = ĥ(T)`. -/
theorem canonHeight_neg (T : curveC.toAffine.Point) : canonHeight (-T) = canonHeight T := by
  have e : hxSeq (-T) = hxSeq T := by
    funext m; rw [hxSeq, hxSeq, neg_nsmul, hx_neg]
  rw [canonHeight_eq, canonHeight_eq, e]

/-- **Basic properties (3).** `ĥ(T + T') = ĥ(T)` for `T' ∈ C(K₀)[2]`. -/
theorem canonHeight_add_twoTorsion (T T' : curveC.toAffine.Point) (hT' : 2 • T' = 0) :
    canonHeight (T + T') = canonHeight T := by
  have h := canonHeight_two_smul (T + T')
  rw [nsmul_add, hT', add_zero, canonHeight_two_smul] at h
  linarith

/-- **Basic properties (4).** `ĥ(T) ≥ 0`. -/
theorem canonHeight_nonneg (T : curveC.toAffine.Point) : 0 ≤ canonHeight T := by
  have := ge_of_tendsto' (hxSeq_tendsto T) fun m =>
    div_nonneg (hx_nonneg ((2 ^ m) • T)) (by positivity : (0 : ℝ) ≤ 4 ^ m)
  linarith

/-! ### The canonical height is quadratic -/

/-- The approximate parallelogram law for `h_x` (Mathlib's, for the naive height `2 h_x`). -/
theorem hx_approx_parallelogram :
    ∃ C, ∀ P Q : curveC.toAffine.Point,
      |hx (P + Q) + hx (P - Q) - 2 * hx P - 2 * hx Q| ≤ C := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law curveC.toAffine
  refine ⟨C / 2, fun P Q => ?_⟩
  have := hC P Q
  simp only [naiveHeight_eq_two_mul_hx] at this
  rw [show 2 * hx (P + Q) + 2 * hx (P - Q) - 2 * (2 * hx P + 2 * hx Q) =
    2 * (hx (P + Q) + hx (P - Q) - 2 * hx P - 2 * hx Q) by ring, abs_mul, abs_two] at this
  linarith

/-- **The parallelogram law** `ĥ(P + Q) + ĥ(P - Q) = 2 ĥ(P) + 2 ĥ(Q)`. -/
theorem canonHeight_parallelogram (P Q : curveC.toAffine.Point) :
    canonHeight (P + Q) + canonHeight (P - Q) = 2 * canonHeight P + 2 * canonHeight Q := by
  obtain ⟨C, hC⟩ := hx_approx_parallelogram
  set e : ℕ → ℝ := fun m =>
    hxSeq (P + Q) m + hxSeq (P - Q) m - 2 * hxSeq P m - 2 * hxSeq Q m with he
  have hlim : Tendsto e atTop
      (𝓝 (2 * canonHeight (P + Q) + 2 * canonHeight (P - Q) - 2 * (2 * canonHeight P) -
        2 * (2 * canonHeight Q))) :=
    (((hxSeq_tendsto _).add (hxSeq_tendsto _)).sub ((hxSeq_tendsto P).const_mul 2)).sub
      ((hxSeq_tendsto Q).const_mul 2)
  have hbound : ∀ m, |e m| ≤ C * (1 / 4) ^ m := by
    intro m
    have h := hC ((2 ^ m) • P) ((2 ^ m) • Q)
    rw [← nsmul_add, ← nsmul_sub] at h
    have e1 : e m = (hx ((2 ^ m) • (P + Q)) + hx ((2 ^ m) • (P - Q)) - 2 * hx ((2 ^ m) • P) -
        2 * hx ((2 ^ m) • Q)) / 4 ^ m := by
      simp only [he, hxSeq]; ring
    rw [e1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ m), one_div_pow,
      ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right h (by positivity)
  have hzero : Tendsto e atTop (𝓝 0) := by
    have hC0 : Tendsto (fun m : ℕ => C * (1 / 4 : ℝ) ^ m) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul C
      simpa using this
    exact squeeze_zero_norm (fun m => by rw [Real.norm_eq_abs]; exact hbound m) hC0
  have := tendsto_nhds_unique hlim hzero
  linarith

@[simp] theorem canonHeight_zero : canonHeight 0 = 0 := by
  have := canonHeight_parallelogram 0 0
  simp only [add_zero, sub_zero] at this
  linarith

theorem canonHeight_nsmul (n : ℕ) (P : curveC.toAffine.Point) :
    canonHeight (n • P) = (n : ℝ) ^ 2 * canonHeight P := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    have h := canonHeight_parallelogram ((n + 1) • P) P
    rw [← succ_nsmul, show (n + 1) • P - P = n • P by rw [succ_nsmul, add_sub_cancel_right]] at h
    rw [ih0, ih1] at h
    push_cast at h ⊢
    linarith

/-- **`ĥ` is quadratic**: `ĥ([m] P) = m² ĥ(P)` for `m ∈ ℤ`. -/
theorem canonHeight_zsmul (m : ℤ) (P : curveC.toAffine.Point) :
    canonHeight (m • P) = (m : ℝ) ^ 2 * canonHeight P := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [natCast_zsmul, canonHeight_nsmul]; push_cast; ring
  · rw [neg_zsmul, canonHeight_neg, natCast_zsmul, canonHeight_nsmul]; push_cast; ring

end ZInQ
