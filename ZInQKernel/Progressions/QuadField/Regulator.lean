/-
Plan step 3.2: the regulator of `ℚ(√d)`: `1` for `d < 0`, at least `log ((1 + √5) / 2)` for
`d > 0`.
-/
import ZInQKernel.Progressions.QuadField.Signature

namespace ZInQ.Progressions

open NumberField NumberField.InfinitePlace NumberField.Units QuadraticAlgebra

/-- A real number `a > 1` with `a² + n = t a` or `a² + n = -t a` for integers `t` and `n = ±1`
is at least the golden ratio. -/
theorem golden_le_of_quadratic {y : ℝ} {t n : ℤ} (hn : n = 1 ∨ n = -1)
    (hy : y ^ 2 - t * y + n = 0) (h1 : 1 < |y|) : (1 + √5) / 2 ≤ |y| := by
  set a := |y| with ha
  have ha2 : a ^ 2 = y ^ 2 := sq_abs y
  have hta : |(t : ℝ)| * a = |y ^ 2 + n| := by
    rw [ha, ← abs_mul]
    congr 1
    linarith
  have hcast : |(t : ℝ)| = ((|t| : ℤ) : ℝ) := by push_cast; rfl
  have ha0 : 0 < a := by linarith
  have hquad : 0 ≤ a ^ 2 - a - 1 := by
    rcases hn with rfl | rfl
    · rw [Int.cast_one, ← ha2, abs_of_pos (by positivity : (0 : ℝ) < a ^ 2 + 1)] at hta
      have h2 : (2 : ℝ) < |(t : ℝ)| := by
        by_contra hc
        have hc' := not_lt.mp hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hc') ha0.le, sq_pos_of_pos (sub_pos.mpr h1)]
      rw [hcast] at h2
      have h3 : (3 : ℤ) ≤ |t| := by
        have : (2 : ℤ) < |t| := by exact_mod_cast h2
        omega
      have h3' : (3 : ℝ) ≤ |(t : ℝ)| := by rw [hcast]; exact_mod_cast h3
      nlinarith [mul_le_mul_of_nonneg_right h3' ha0.le]
    · have hpos : (0 : ℝ) < a ^ 2 - 1 := by nlinarith
      rw [Int.cast_neg, Int.cast_one, ← sub_eq_add_neg, ← ha2, abs_of_pos hpos] at hta
      have h2 : (0 : ℝ) < |(t : ℝ)| := by
        by_contra hc
        have hc' := not_lt.mp hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hc') ha0.le]
      rw [hcast] at h2
      have h3 : (1 : ℤ) ≤ |t| := by
        have : (0 : ℤ) < |t| := by exact_mod_cast h2
        omega
      have h3' : (1 : ℝ) ≤ |(t : ℝ)| := by rw [hcast]; exact_mod_cast h3
      nlinarith [mul_le_mul_of_nonneg_right h3' ha0.le]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 0 ≤ √5 := Real.sqrt_nonneg 5
  by_contra hc
  have hc := not_le.mp hc
  have hneg : (a - (1 + √5) / 2) * (a - (1 - √5) / 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  nlinarith

/-- A real root `y` of `X² - tX + n`, with `t` an integer and `n = ±1`, satisfies
`|log |y|| ≥ log ((1 + √5) / 2)` unless `|y| = 1`. -/
theorem log_golden_le_abs_log {y : ℝ} {t n : ℤ} (hn : n = 1 ∨ n = -1)
    (hy : y ^ 2 - t * y + n = 0) (h1 : |y| ≠ 1) :
    Real.log ((1 + √5) / 2) ≤ |Real.log (|y|)| := by
  have hg : 0 < (1 + √5) / 2 := by positivity
  have hy0 : y ≠ 0 := by
    rintro rfl
    rcases hn with rfl | rfl <;> norm_num at hy
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · -- `|y| < 1`: pass to `1 / y`, a root of `X² - (t n) X + n`.
    set z := y⁻¹ with hz
    have hz' : z ^ 2 - ((t * n : ℤ) : ℝ) * z + n = 0 := by
      have hn2 : (n : ℝ) * n = 1 := by rcases hn with rfl | rfl <;> norm_num
      have : (z ^ 2 - ((t * n : ℤ) : ℝ) * z + n) * y ^ 2 = n * (y ^ 2 - t * y + n) := by
        rw [hz]
        field_simp
        push_cast
        linear_combination (-1 : ℝ) * hn2
      rw [hy, mul_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hy0
    have hzgt : 1 < |z| := by
      rw [hz, abs_inv]
      exact (one_lt_inv₀ (abs_pos.mpr hy0)).mpr hlt
    have := golden_le_of_quadratic hn hz' hzgt
    have hlog : Real.log |y| = -Real.log |z| := by
      rw [hz, abs_inv, Real.log_inv, neg_neg]
    rw [hlog, abs_neg, abs_of_pos (Real.log_pos hzgt)]
    exact Real.log_le_log hg this
  · have := golden_le_of_quadratic hn hy hgt
    rw [abs_of_pos (Real.log_pos hgt)]
    exact Real.log_le_log hg this

variable {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]

/-- The trace `2x` and the norm `x² - d y²` of an algebraic integer `x + y√d` are integers. -/
theorem Qsqrt.exists_int_trace_norm (x : 𝓞 (Qsqrt d)) :
    ∃ t n : ℤ, trace (x : Qsqrt d) = t ∧ norm (x : Qsqrt d) = n := by
  have hx : IsIntegral ℤ (x : Qsqrt d) := x.isIntegral_coe
  have hs : IsIntegral ℤ (star (x : Qsqrt d)) := map_isIntegral_int (starRingEnd _) hx
  have ht : IsIntegral ℤ (trace (x : Qsqrt d)) := by
    rw [← isIntegral_algebraMap_iff (B := Qsqrt d), algebraMap_trace_eq_add_star]
    exact hx.add hs
  have hn : IsIntegral ℤ (norm (x : Qsqrt d)) := by
    rw [← isIntegral_algebraMap_iff (B := Qsqrt d), algebraMap_norm_eq_mul_star]
    exact hx.mul hs
  obtain ⟨t, ht'⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  exact ⟨t, n, by simp [← ht'], by simp [← hn']⟩

/-- A unit `u` of the ring of integers of `ℚ(√d)` is a root, under every real embedding, of
`X² - tX + n` with `t` an integer and `n = ±1`. -/
theorem Qsqrt.unit_quadratic (u : (𝓞 (Qsqrt d))ˣ) :
    ∃ t n : ℤ, (n = 1 ∨ n = -1) ∧ ∀ ψ : Qsqrt d →+* ℝ,
      ψ (u : Qsqrt d) ^ 2 - t * ψ (u : Qsqrt d) + n = 0 := by
  obtain ⟨t, n, ht, hn⟩ := Qsqrt.exists_int_trace_norm (u : 𝓞 (Qsqrt d))
  obtain ⟨t', n', -, hn'⟩ := Qsqrt.exists_int_trace_norm ((u⁻¹ : (𝓞 (Qsqrt d))ˣ) : 𝓞 (Qsqrt d))
  have hmul : n * n' = 1 := by
    have h1 : norm ((u : 𝓞 (Qsqrt d)) : Qsqrt d) *
        norm (((u⁻¹ : (𝓞 (Qsqrt d))ˣ) : 𝓞 (Qsqrt d)) : Qsqrt d) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    rw [hn, hn'] at h1
    exact_mod_cast h1
  refine ⟨t, n, Int.eq_one_or_neg_one_of_mul_eq_one hmul, fun ψ => ?_⟩
  have hq : ∀ q : ℚ, ψ (algebraMap ℚ (Qsqrt d) q) = q := fun q =>
    eq_ratCast (ψ.comp (algebraMap ℚ (Qsqrt d))) q
  have h := congrArg ψ (sq_sub_trace_smul_add_norm_eq_zero ((u : 𝓞 (Qsqrt d)) : Qsqrt d))
  rw [map_zero, map_add, map_sub, map_pow, Algebra.smul_def, map_mul, hq, hq, ht, hn] at h
  simpa using h

/-- The regulator of an imaginary quadratic field is `1`. -/
theorem Qsqrt.regulator_of_neg (hd : d < 0) : regulator (Qsqrt d) = 1 := by
  classical
  have hcard : Fintype.card (InfinitePlace (Qsqrt d)) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, Qsqrt.nrRealPlaces_of_neg hd,
      Qsqrt.nrComplexPlaces_of_neg hd]
  obtain ⟨w'⟩ : Nonempty (InfinitePlace (Qsqrt d)) := inferInstance
  have : IsEmpty {w : InfinitePlace (Qsqrt d) // w ≠ w'} := by
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
    exact ⟨fun ⟨w, hw⟩ => hw ((hx w).trans (hx w').symm)⟩
  have hrank : rank (Qsqrt d) = 0 := by simp [rank, hcard]
  have : IsEmpty (Fin (rank (Qsqrt d))) := by rw [hrank]; infer_instance
  rw [regulator_eq_det (Qsqrt d) w' (Equiv.equivOfIsEmpty _ _), Matrix.det_isEmpty, abs_one]

/-- The regulator of a real quadratic field is at least `log ((1 + √5) / 2)`. -/
theorem Qsqrt.regulator_ge_of_pos (hd : 0 < d) :
    Real.log ((1 + √5) / 2) ≤ regulator (Qsqrt d) := by
  classical
  have htr := Qsqrt.isTotallyReal hd
  have hcard : Fintype.card (InfinitePlace (Qsqrt d)) = 2 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, Qsqrt.nrRealPlaces_of_pos hd,
      Qsqrt.nrComplexPlaces_of_pos hd]
  have hrank : rank (Qsqrt d) = 1 := by simp [rank, hcard]
  obtain ⟨w'⟩ : Nonempty (InfinitePlace (Qsqrt d)) := inferInstance
  have hcard' : Fintype.card {w : InfinitePlace (Qsqrt d) // w ≠ w'} = 1 := by
    rw [Fintype.card_subtype_compl, hcard, Fintype.card_subtype_eq]
  let e₁ := Fintype.equivFinOfCardEq hcard'
  have : Unique {w : InfinitePlace (Qsqrt d) // w ≠ w'} := e₁.unique
  let e := e₁.trans (finCongr hrank.symm)
  have hreg := regulator_eq_det (Qsqrt d) w' e
  rw [Matrix.det_unique, Matrix.of_apply] at hreg
  set w : {w : InfinitePlace (Qsqrt d) // w ≠ w'} := default
  set ε := fundSystem (Qsqrt d) (e w)
  have hw : IsReal w.val := htr.isReal _
  rw [hw.mult_eq_one, Nat.cast_one, one_mul] at hreg
  set ψ := embedding_of_isReal hw
  have hψ : w.val (ε : Qsqrt d) = |ψ (ε : Qsqrt d)| := by
    rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs]
  rw [hψ] at hreg
  have hne : |ψ (ε : Qsqrt d)| ≠ 1 := by
    intro h1
    have := regulator_pos (Qsqrt d)
    rw [hreg, h1, Real.log_one, abs_zero] at this
    exact lt_irrefl _ this
  obtain ⟨t, n, hn, hq⟩ := Qsqrt.unit_quadratic ε
  rw [hreg]
  exact log_golden_le_abs_log hn (hq ψ) hne

end ZInQ.Progressions
