import ZInQKernel.Assembly.Close.Relation
import ZInQKernel.Assembly.Real

/-!
# Completeness of Close for every fixed shift

Blueprint: `assembly/approximation/close-completeness.md`.

For every `n ∈ ℤ ∖ 𝒞` and every nonzero `κ ∈ ℤ`, `Rel_close(ι(n), ι(κ), n)` (`close_complete`).
Put `θ = 4^{-𝓑(n, κ)}/4`. First `l ≥ 1` with `ε_l < θ` (`exists_epsIdx_lt`): on `y² = x³ - d²x`,
`σ(z)² = σ(x)/(σ(x)² - σ(d)²)` is small when `σ(x)` is large at both real places
(`exists_abs_emb_z_lt`), the accumulation statement gives such a multiple `[l]P₀`, and
`ε_l = |u_l| + |v_l| ≤ |σ₊ z_l| + |σ₋ z_l|` (`abs_re_add_abs_im_le`). Then `a ≥ 1` with
`|r(a, n a) - n| < ε_l` (`exists_rRatio_close`), from the real derivative statement at both
places and `r(a, n a) = (σ₊ + σ₋)(z_{na}/z_a)/2`. The order of the choices matters: `l` first,
then `a` depending on `ε_l`. The constant `𝓑(n, κ)` is never evaluated.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine Syntax Translation Compiler.Precision

/-- The two coordinate functions `z = -x/y` agree (`Compiler.Precision.zPt` and `zCoord`). -/
theorem zPt_eq_zCoord (P : genCurve.toAffine.Point) : zPt P = zCoord P := by
  cases P <;> rfl

/-- `|u| + |v| ≤ |σ₊(w)| + |σ₋(w)|` for `w = u + v s ∈ K₀`. -/
theorem abs_re_add_abs_im_le (w : K0) :
    |(w.re : ℝ)| + |(w.im : ℝ)| ≤ |K0.embPlus w| + |K0.embMinus w| := by
  rw [K0.embPlus_apply, K0.embMinus_apply]
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  set P := (w.re : ℝ) + w.im * Real.sqrt 2
  set M := (w.re : ℝ) - w.im * Real.sqrt 2
  have h1 : |(w.re : ℝ)| * 2 ≤ |P| + |M| := by
    calc |(w.re : ℝ)| * 2 = |(w.re : ℝ) * 2| := by rw [abs_mul, abs_two]
      _ = |P + M| := by congr 1; simp only [P, M]; ring
      _ ≤ |P| + |M| := abs_add_le _ _
  have h2 : |(w.im : ℝ)| * (2 * Real.sqrt 2) ≤ |P| + |M| := by
    calc |(w.im : ℝ)| * (2 * Real.sqrt 2) = |(w.im : ℝ) * (2 * Real.sqrt 2)| := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt 2)]
      _ = |P - M| := by congr 1; simp only [P, M]; ring
      _ ≤ |P| + |M| := abs_sub _ _
  have h3 : |(w.im : ℝ)| ≤ |(w.im : ℝ)| * Real.sqrt 2 := le_mul_of_one_le_right (abs_nonneg _) hs
  nlinarith

/-- Near `O` at a real place `σ`, the local parameter is small: for every `θ > 0` there is `M`
such that every affine `(x, y) ∈ E(K₀)` with `σ(x) > M` has `|σ(-x/y)| < θ`. -/
theorem exists_abs_emb_z_lt (σ : K0 →+* ℝ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ (x y : K0) (_ : genCurve.toAffine.Nonsingular x y), M < σ x →
      |σ (-x / y)| < θ := by
  refine ⟨2 * |σ genD| + 1 + 2 / θ ^ 2, fun x y h hx => ?_⟩
  have hc := congrArg σ (genCurve_sq_genA h)
  simp only [map_pow, map_add, map_mul, genA, map_neg] at hc
  set D := σ genD
  set X := σ x
  set Y := σ y
  have hθ2 : 0 < θ ^ 2 := by positivity
  have hq : 0 < 2 / θ ^ 2 := by positivity
  have hDX : |D| ≤ X / 2 := by linarith [abs_nonneg D]
  have hX : 0 < X := by linarith [abs_nonneg D]
  have hD2 : D ^ 2 ≤ X ^ 2 / 4 := by
    rw [← sq_abs D]
    nlinarith [abs_nonneg D]
  have hY2 : 3 * X ^ 3 / 4 ≤ Y ^ 2 := by
    rw [hc]; nlinarith
  have hθX : 2 < θ ^ 2 * X := by
    have : 2 / θ ^ 2 < X := by linarith [abs_nonneg D]
    rwa [div_lt_iff₀ hθ2, mul_comm] at this
  have hY0 : 0 < Y ^ 2 := lt_of_lt_of_le (by positivity) hY2
  have hYne : Y ≠ 0 := fun h0 => by rw [h0] at hY0; simp at hY0
  rw [map_div₀, map_neg, abs_div, abs_neg, div_lt_iff₀ (abs_pos.2 hYne)]
  refine abs_lt_of_sq_lt_sq ?_ (by positivity)
  rw [mul_pow, sq_abs]
  have hX2 : 0 < X ^ 2 := by positivity
  calc X ^ 2 < (3 / 4) * (θ ^ 2 * X) * X ^ 2 := by nlinarith
    _ = θ ^ 2 * (3 * X ^ 3 / 4) := by ring
    _ ≤ θ ^ 2 * Y ^ 2 := by gcongr

/-- **Choice of `l`.** For every `θ > 0` there is `l ≥ 1` with `ε_l < θ`. -/
theorem exists_epsIdx_lt {θ : ℝ} (hθ : 0 < θ) : ∃ l : ℕ, 1 ≤ l ∧ (epsIdx l : ℝ) < θ := by
  obtain ⟨Mp, hMp⟩ := exists_abs_emb_z_lt K0.embPlus (half_pos hθ)
  obtain ⟨Mm, hMm⟩ := exists_abs_emb_z_lt K0.embMinus (half_pos hθ)
  obtain ⟨l, hl, x, y, h, hP, hxp, hxm⟩ :=
    exists_multiple_large genP0_not_isOfFinAddOrder (max Mp Mm)
  refine ⟨l, hl, ?_⟩
  have hz : zIdx l = -x / y := by rw [zIdx, hP, zPt_some]
  have hb := abs_re_add_abs_im_le (zIdx l)
  have he : (epsIdx l : ℝ) = |((zIdx l).re : ℝ)| + |((zIdx l).im : ℝ)| := by
    rw [epsIdx]; push_cast; rfl
  rw [he]
  rw [hz] at hb ⊢
  linarith [hMp x y h (lt_of_le_of_lt (le_max_left _ _) hxp),
    hMm x y h (lt_of_le_of_lt (le_max_right _ _) hxm)]

/-- **Choice of `a`.** For `n ≠ 0` and `η > 0` there is `a ≥ 1` with `|r(a, n a) - n| < η`. -/
theorem exists_rRatio_close {n : ℤ} (hn : n ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ a : ℕ, 1 ≤ a ∧ |(rRatio a (n * a) : ℝ) - n| < η := by
  obtain ⟨Mp, hMp⟩ := z_ratio_tendsto K0.embPlus hn hη
  obtain ⟨Mm, hMm⟩ := z_ratio_tendsto K0.embMinus hn hη
  obtain ⟨a, ha, x, y, h, hP, hxp, hxm⟩ :=
    exists_multiple_large genP0_not_isOfFinAddOrder (max Mp Mm)
  refine ⟨a, ha, ?_⟩
  obtain ⟨-, -, -, dp⟩ := hMp x y h (lt_of_le_of_lt (le_max_left _ _) hxp)
  obtain ⟨-, -, -, dm⟩ := hMm x y h (lt_of_le_of_lt (le_max_right _ _) hxm)
  have hq : zIdx (n * a) / zIdx a = zCoord (n • Point.some x y h) / zCoord (Point.some x y h) := by
    rw [zIdx, zIdx, mul_zsmul, hP, zPt_eq_zCoord, zPt_eq_zCoord]
  rw [← hq] at dp dm
  set w := zIdx (n * a) / zIdx a
  have hre : (rRatio a (n * a) : ℝ) = (K0.embPlus w + K0.embMinus w) / 2 := by
    rw [rRatio, K0.embPlus_apply, K0.embMinus_apply]; ring
  rw [hre, show (K0.embPlus w + K0.embMinus w) / 2 - n =
    ((K0.embPlus w - n) + (K0.embMinus w - n)) / 2 by ring, abs_div, abs_two,
    div_lt_iff₀ two_pos]
  calc |(K0.embPlus w - n) + (K0.embMinus w - n)| ≤ |K0.embPlus w - n| + |K0.embMinus w - n| :=
        abs_add_le _ _
    _ < η * 2 := by linarith

/-- **Completeness of Close for every fixed shift.** Under M, for every `n ∈ ℤ ∖ 𝒞` and every
nonzero `κ ∈ ℤ`, `Rel_close(ι(n), ι(κ), n)`. -/
theorem close_complete
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value)
    (n κ : ℤ) (hn : (n : ℚ) ∉ contactSet) (hκ : κ ≠ 0) :
    ValRel (getEx closeSpecLib 2) (List.ofFn (iota n) ++ (List.ofFn (iota κ) ++ [(n : ℚ)])) := by
  have hnC : n ∉ contacts := (cast_mem_contactSet_iff n).not.1 hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hnC (by decide)
  set B := bound n κ
  have h4 : (0 : ℝ) < 4 ^ B := by positivity
  obtain ⟨l, hl, hεl⟩ := exists_epsIdx_lt (θ := ((4 : ℝ) ^ B)⁻¹ / 4) (by positivity)
  have hladm : Admissible (l : ℤ) := admissible_of_ne_zero (by omega)
  have hε : (0 : ℝ) < epsIdx l := by exact_mod_cast epsIdx_pos hladm
  obtain ⟨a, ha, hr⟩ := exists_rRatio_close hn0 hε
  have hclose : |rRatio a (n * a) - n| < epsIdx l := by exact_mod_cast hr
  have hprec : 4 * epsIdx l * 4 ^ B < 1 := by
    have : 4 * (epsIdx l : ℝ) * 4 ^ B < 1 := by
      calc 4 * (epsIdx l : ℝ) * 4 ^ B < 4 * (((4 : ℝ) ^ B)⁻¹ / 4) * 4 ^ B := by gcongr
        _ = 1 := by field_simp
    exact_mod_cast this
  refine (close_relation_iff hM _ _ _).2 ⟨n, κ, a, l, rfl, rfl,
    (accepts_enc_iff _ _ _ _ _).2 ⟨⟨hnC, hκ, by omega, by omega, rfl⟩,
      ⟨hladm, admissible_of_ne_zero (by omega), admissible_of_ne_zero (mul_ne_zero hn0 (by omega))⟩,
      hclose, hprec⟩, by rw [abs_sub_comm]; exact hclose⟩

end ZInQ.Assembly
