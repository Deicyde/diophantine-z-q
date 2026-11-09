import ZInQKernel.Model.DivisionPolynomials.MulByN
import ZInQKernel.Model.DivisionPolynomials.Classical
import ZInQKernel.Model.Field.Curve

/-!
# The derivative of multiplication at a real place

Blueprint: `assembly/approximation/real-derivative.md`.

For a real embedding `τ` of `K₀`, a nonzero integer `n` and `η > 0` there is `M` such that every
affine `Q = (x, y) ∈ E(K₀)` with `τ(x) > M` has `x, y ≠ 0`, `[n]Q` affine with nonzero
coordinates, and `|τ(z([n]Q)/z(Q)) - n| < η`, where `z = -x/y` (`zCoord`).

For `n ≥ 1` the multiplication formulas give `z([n]Q)/z(Q) = Φ_n(x) ΨSq_n(x) / (x f_{2n}(x))`
with Mathlib's `Φ_n`, `ΨSq_n` and `f_{2n} = preΨ'_{2n}` of `y² = x³ + Ax`, `A = -d²`. Numerator
and denominator have degree `2n² - 1` and leading coefficients `n²` and `n`, so the quotient
tends to `n` at `+∞` (`Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq`).
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine Filter Topology Polynomial
open ZInQ.Syntax (WA psiEval normDiv psiEval_eq normDiv_eq_preΨ' WA_Ψ₂Sq)

/-- The coordinate `z = -x/y` of a point of `E(K₀)`; the junk value at `O` is `0`. -/
noncomputable def zCoord : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x y _ => -x / y

@[simp] theorem zCoord_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    zCoord (.some x y h) = -x / y := rfl

/-! ### The multiplication formulas as univariate polynomials -/

section Formulas

variable {R : Type*} [CommRing R] (A : R)

theorem psiEval_natCast (k : ℕ) (x y : R) :
    psiEval A k x y = (normDiv A k).eval x * if Even k then 2 * y else 1 := by
  rw [psiEval_eq]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp [Int.sign_natCast_of_ne_zero hk.ne', Int.even_coe_nat]

/-- `ψ_k(x, y)² = ΨSq_k(x)` on `y² = x³ + Ax`. -/
theorem psiEval_sq (k : ℕ) {x y : R} (hc : y ^ 2 = x ^ 3 + A * x) :
    psiEval A k x y ^ 2 = ((WA A).ΨSq k).eval x := by
  rw [psiEval_natCast, ΨSq_ofNat, ← normDiv_eq_preΨ', WA_Ψ₂Sq]
  split_ifs
  · simp only [eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_ofNat]
    linear_combination (4 * (normDiv A k).eval x ^ 2) * hc
  · simp

/-- `x ψ_{m+1}² - ψ_{m+2} ψ_m = Φ_{m+1}(x)` on `y² = x³ + Ax`. -/
theorem psiEval_phi (m : ℕ) {x y : R} (hc : y ^ 2 = x ^ 3 + A * x) :
    x * psiEval A ((m : ℤ) + 1) x y ^ 2 -
        psiEval A ((m : ℤ) + 1 + 1) x y * psiEval A ((m : ℤ) + 1 - 1) x y =
      ((WA A).Φ ((m : ℤ) + 1)).eval x := by
  rw [Φ_ofNat, show ((m : ℤ) + 1 + 1) = ((m + 2 : ℕ) : ℤ) by push_cast; ring,
    show ((m : ℤ) + 1 - 1) = ((m : ℕ) : ℤ) by ring,
    show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
    psiEval_natCast, psiEval_natCast, psiEval_natCast]
  simp only [← normDiv_eq_preΨ', WA_Ψ₂Sq]
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : ¬Even (m + 1) := by simp [Nat.even_add_one, hm]
    have h2 : Even (m + 2) := by simpa [Nat.even_add] using hm
    simp only [h1, h2, hm, ite_true, ite_false]
    simp only [eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_ofNat, eval_one]
    linear_combination (-4 * (normDiv A (m + 2)).eval x * (normDiv A m).eval x) * hc
  · have hm' : ¬Even m := Nat.not_even_iff_odd.mpr hm
    have h1 : Even (m + 1) := by simp [Nat.even_add_one, hm']
    have h2 : ¬Even (m + 2) := by simpa [Nat.even_add] using hm'
    simp only [h1, h2, hm', ite_true, ite_false]
    simp only [eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_ofNat, eval_one]
    linear_combination (4 * x * (normDiv A (m + 1)).eval x ^ 2) * hc

/-- `ψ_{2(m+1)}(x, y) = 2y f_{2(m+1)}(x)`. -/
theorem psiEval_double (m : ℕ) (x y : R) :
    psiEval A (2 * ((m : ℤ) + 1)) x y = 2 * y * ((WA A).preΨ' (2 * (m + 1))).eval x := by
  rw [show (2 * ((m : ℤ) + 1)) = ((2 * (m + 1) : ℕ) : ℤ) by push_cast; ring, psiEval_natCast,
    normDiv_eq_preΨ', ite_eq_left (even_two_mul _)]
  ring

end Formulas

/-! ### Degrees and leading coefficients -/

section Degrees

variable {F : Type*} [Field F] [CharZero F] (A : F) (m : ℕ)

/-- The numerator `Φ_{m+1} ΨSq_{m+1}`. -/
noncomputable def zNum : F[X] := (WA A).Φ ((m : ℤ) + 1) * (WA A).ΨSq ((m : ℤ) + 1)

/-- The denominator `x f_{2(m+1)}`. -/
noncomputable def zDen : F[X] := X * (WA A).preΨ' (2 * (m + 1))

theorem cast_ne_zero : (((m : ℤ) + 1 : ℤ) : F) ≠ 0 := by
  push_cast; exact_mod_cast Nat.succ_ne_zero m

theorem cast_two_ne_zero : ((2 * (m + 1) : ℕ) : F) ≠ 0 := by
  exact_mod_cast (by omega : 2 * (m + 1) ≠ 0)

theorem zNum_ne_zero : zNum A m ≠ 0 :=
  mul_ne_zero (fun h => by simpa [h] using (WA A).leadingCoeff_Φ ((m : ℤ) + 1))
    ((WA A).ΨSq_ne_zero (cast_ne_zero m))

theorem zDen_ne_zero : zDen A m ≠ 0 :=
  mul_ne_zero X_ne_zero ((WA A).preΨ'_ne_zero (cast_two_ne_zero m))

theorem natDegree_zNum : (zNum A m).natDegree = 2 * (m + 1) ^ 2 - 1 := by
  rw [zNum, natDegree_mul (fun h => by simpa [h] using (WA A).leadingCoeff_Φ ((m : ℤ) + 1))
    ((WA A).ΨSq_ne_zero (cast_ne_zero m)), natDegree_Φ, natDegree_ΨSq _ (cast_ne_zero m),
    show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  have : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos m)
  omega

theorem natDegree_zDen : (zDen A m).natDegree = 2 * (m + 1) ^ 2 - 1 := by
  rw [zDen, natDegree_mul X_ne_zero ((WA A).preΨ'_ne_zero (cast_two_ne_zero m)), natDegree_X,
    natDegree_preΨ' _ (cast_two_ne_zero m), ite_eq_left (even_two_mul _)]
  have h4 : (2 * (m + 1)) ^ 2 = 4 * (m + 1) ^ 2 := by ring
  have : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos m)
  rw [h4]
  omega

theorem degree_zNum_eq : (zNum A m).degree = (zDen A m).degree := by
  rw [degree_eq_natDegree (zNum_ne_zero A m), degree_eq_natDegree (zDen_ne_zero A m),
    natDegree_zNum, natDegree_zDen]

theorem leadingCoeff_zNum : (zNum A m).leadingCoeff = ((m : F) + 1) ^ 2 := by
  rw [zNum, leadingCoeff_mul, leadingCoeff_Φ, leadingCoeff_ΨSq _ (cast_ne_zero m)]
  push_cast; ring

theorem leadingCoeff_zDen : (zDen A m).leadingCoeff = (m : F) + 1 := by
  rw [zDen, leadingCoeff_mul, leadingCoeff_X, leadingCoeff_preΨ' _ (cast_two_ne_zero m),
    ite_eq_left (even_two_mul _), Nat.mul_div_cancel_left _ two_pos]
  push_cast; ring

end Degrees

/-! ### The limit -/

theorem genCurve_sq_genA {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + genA * x := by
  have := (genCurve_equation_iff x y).mp h.1
  rw [genA]; linear_combination this

/-- The derivative of `[m + 1]` at the identity, at a real place. -/
theorem z_ratio_tendsto_succ (τ : K0 →+* ℝ) (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∀ (x y : K0) (h : genCurve.toAffine.Nonsingular x y), M < τ x →
      x ≠ 0 ∧ y ≠ 0 ∧
      (∃ (x' y' : K0) (h' : genCurve.toAffine.Nonsingular x' y'),
        ((m : ℤ) + 1) • Point.some x y h = .some x' y' h' ∧ x' ≠ 0 ∧ y' ≠ 0) ∧
      |τ (zCoord (((m : ℤ) + 1) • Point.some x y h) / zCoord (.some x y h)) - ((m : ℝ) + 1)| < η := by
  set P := zNum genA m
  set Q := zDen genA m
  have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hlim : Tendsto (fun t => eval t (P.map τ) / eval t (Q.map τ)) atTop (𝓝 ((m : ℝ) + 1)) := by
    have := div_tendsto_atTop_leadingCoeff_div_of_degree_eq (P := P.map τ) (Q := Q.map τ)
      (by rw [degree_map, degree_map, degree_zNum_eq])
    rwa [leadingCoeff_map, leadingCoeff_map, leadingCoeff_zNum, leadingCoeff_zDen, map_pow,
      map_add, map_natCast, map_one, sq, mul_div_assoc, div_self hm0, mul_one] at this
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim.eventually (Metric.ball_mem_nhds _ hη)).and
    ((hlim.eventually_ne hm0).and (eventually_gt_atTop (|τ genD| + 1))))
  refine ⟨N, fun x y h hx => ?_⟩
  obtain ⟨hball, hne, hgt⟩ := hN (τ x) hx.le
  simp only [eval_map, eval₂_at_apply] at hball hne
  obtain ⟨hP, hQ⟩ := div_ne_zero_iff.mp hne
  have hP' := (map_ne_zero τ).mp hP
  have hQ' := (map_ne_zero τ).mp hQ
  simp only [P, Q, zNum, zDen, eval_mul, eval_X] at hP' hQ'
  obtain ⟨hΦ, hS⟩ := mul_ne_zero_iff.mp hP'
  obtain ⟨hx0, hF⟩ := mul_ne_zero_iff.mp hQ'
  have hc := genCurve_sq_genA h
  -- `y ≠ 0` since `τ(y)² = τ(x)(τ(x)² - τ(d)²) > 0`
  have hy0 : y ≠ 0 := by
    intro hy
    have h1 := congrArg τ hc
    simp only [hy, map_pow, map_add, map_mul, genA, map_neg, map_zero] at h1
    have ht : 0 < τ x := by linarith [abs_nonneg (τ genD)]
    have ht2 : τ genD ^ 2 < τ x ^ 2 := by
      rw [← sq_abs (τ genD)]
      exact pow_lt_pow_left₀ (by linarith) (abs_nonneg _) two_ne_zero
    have : 0 < τ x * (τ x ^ 2 - τ genD ^ 2) := mul_pos ht (by linarith)
    nlinarith
  -- the multiplication formulas
  have hsq := psiEval_sq genA (m + 1) hc
  push_cast at hsq
  have hphi := psiEval_phi genA m hc
  have hdbl := psiEval_double genA m x y
  set ψ := psiEval genA ((m : ℤ) + 1) x y with hψdef
  have hψ : ψ ≠ 0 := by
    intro h0; apply hS; rw [← hsq, h0]; ring
  obtain ⟨h1, h2⟩ := mulByN_formulas x y h ((m : ℤ) + 1) (by positivity)
  have hnP : ((m : ℤ) + 1) • Point.some x y h ≠ 0 := fun h0 => hψ (h1.mp h0)
  obtain ⟨h', heq⟩ := h2 hnP
  set S := ((WA genA).ΨSq ((m : ℤ) + 1)).eval x
  set Φx := ((WA genA).Φ ((m : ℤ) + 1)).eval x
  set Fx := ((WA genA).preΨ' (2 * (m + 1))).eval x
  have ex : x - psiEval genA ((m : ℤ) + 1 + 1) x y * psiEval genA ((m : ℤ) + 1 - 1) x y / ψ ^ 2 =
      Φx / S := by
    rw [← hsq, ← hphi]; field_simp
  have ey : psiEval genA (2 * ((m : ℤ) + 1)) x y / (2 * ψ ^ 4) = y * Fx / S ^ 2 := by
    rw [hdbl, ← hsq]; field_simp
  refine ⟨hx0, hy0, ⟨_, _, h', heq, by rw [ex]; exact div_ne_zero hΦ hS,
    by rw [ey]; exact div_ne_zero (mul_ne_zero hy0 hF) (pow_ne_zero 2 hS)⟩, ?_⟩
  rw [heq, zCoord_some, zCoord_some, ex, ey]
  have hr : -(Φx / S) / (y * Fx / S ^ 2) / (-x / y) = Φx * S / (x * Fx) := by
    field_simp
  rw [hr, map_div₀, map_mul, map_mul, ← Real.dist_eq]
  simpa only [P, Q, zNum, zDen, eval_mul, eval_X, map_mul] using hball

/-- **The derivative of multiplication at a real place.** For a real embedding `τ` of `K₀`, a
nonzero integer `n` and `η > 0` there is `M` such that every affine point `Q = (x, y) ∈ E(K₀)`
with `τ(x) > M` has `x ≠ 0`, `y ≠ 0`, `[n]Q` affine with nonzero abscissa and ordinate, and
`|τ(z([n]Q)/z(Q)) - n| < η`, where `z = -x/y`. -/
theorem z_ratio_tendsto (τ : K0 →+* ℝ) {n : ℤ} (hn : n ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∀ (x y : K0) (h : genCurve.toAffine.Nonsingular x y), M < τ x →
      x ≠ 0 ∧ y ≠ 0 ∧
      (∃ (x' y' : K0) (h' : genCurve.toAffine.Nonsingular x' y'),
        n • Point.some x y h = .some x' y' h' ∧ x' ≠ 0 ∧ y' ≠ 0) ∧
      |τ (zCoord (n • Point.some x y h) / zCoord (.some x y h)) - n| < η := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 ∨ n = -((m : ℤ) + 1) := by
    rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
    · exact ⟨k - 1, Or.inl (by omega)⟩
    · exact ⟨k - 1, Or.inr (by omega)⟩
  · obtain ⟨M, hM⟩ := z_ratio_tendsto_succ τ m hη
    refine ⟨M, fun x y h hx => ?_⟩
    obtain ⟨a, b, c, d⟩ := hM x y h hx
    exact ⟨a, b, c, by push_cast; exact d⟩
  · obtain ⟨M, hM⟩ := z_ratio_tendsto_succ τ m hη
    refine ⟨M, fun x y h hx => ?_⟩
    obtain ⟨a, b, ⟨x', y', h', heq, hx', hy'⟩, d⟩ := hM x y h hx
    have hneg : genCurve.toAffine.negY x' y' = -y' := shortCurve_negY _ _ _
    refine ⟨a, b, ⟨x', _, _, by rw [neg_zsmul, heq, Point.neg_some], hx',
      by rw [hneg]; exact neg_ne_zero.mpr hy'⟩, ?_⟩
    rw [heq, zCoord_some] at d
    rw [neg_zsmul, heq, Point.neg_some, zCoord_some, zCoord_some, hneg]
    have e1 : -x' / -y' / (-x / y) = -(-x' / y' / (-x / y)) := by ring
    rw [e1, map_neg]
    push_cast
    rw [show ∀ a b : ℝ, -a - -b = -(a - b) by intros; ring, abs_neg]
    exact d

end ZInQ.Assembly
