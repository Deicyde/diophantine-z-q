import ZInQKernel.Model.DivisionPolynomials.Generic

/-!
# Division polynomials compute multiples

Blueprint: `model/field/division-polynomial-multiples.md` (general version).

For an affine point `P = (x, y)` of `y² = x³ + Ax` over a field of characteristic zero and every
integer `n`, `[n]P = O` iff `ψ_n(P) = 0`, and otherwise
`[n]P = (x - ψ_{n+1}ψ_{n-1}/ψ_n², ψ_{2n}/(2ψ_n⁴))`.

Proof: by double-and-add induction, the Jacobian triple `jac n = (4φ_n, 4c_n, 2ψ_n)` is a
nonsingular representative of `[n]P` (`jac_spec`), using Mathlib's Jacobian group law and the
identities `jac_identities`. No case distinction on torsion is needed: Mathlib's `dblXYZ` and
`addXYZ` are valid for all nonsingular representatives, including those of `O`.
-/

namespace ZInQ.DivisionPolynomials

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial
open ZInQ.Syntax (WA psiEval psiEval_eq normDiv divD0 divF3 divF4)

local notation3 "X" => (0 : Fin 3)
local notation3 "Y" => (1 : Fin 3)
local notation3 "Z" => (2 : Fin 3)

variable {K : Type*} [Field K]

/-- On the curve, the blueprint's `ψ_n(x, y)` is the normalized EDS value `w A x y n`. -/
lemma psiEval_eq_w {A x y : K} (hy : y ^ 2 = x ^ 3 + A * x) (n : ℤ) :
    psiEval A n x y = w A x y n := by
  have hb : (divD0 A).eval x = (2 * y) ^ 4 := by
    simp only [divD0, eval_mul, eval_pow, eval_add, eval_X, eval_C, eval_ofNat]
    linear_combination (-16 * (y ^ 2 + (x ^ 3 + A * x))) * hy
  have hk : ∀ k : ℕ, (normDiv A k).eval x =
      preNormEDS' ((2 * y) ^ 4) ((divF3 A).eval x) ((divF4 A).eval x) k := by
    intro k
    rw [normDiv, ← coe_evalRingHom, map_preNormEDS', coe_evalRingHom, hb]
  rw [psiEval_eq, w, normEDS, preNormEDS, hk]
  ring

variable {A : K}

lemma jac_zero (x y : K) : jac A x y 0 = (2 : K) • ![1, 1, 0] := by
  ext i
  fin_cases i <;> simp [jac, phiw, cw, smul_fin3, w_neg] <;> norm_num

lemma jac_one (x y : K) : jac A x y 1 = (2 : K) • ![x, y, 1] := by
  ext i
  fin_cases i
  · simp [jac, phiw, smul_fin3]; norm_num
  · simp [jac, cw, smul_fin3]; ring
  · simp [jac, smul_fin3]

variable [CharZero K] [DecidableEq K]

/-- `jac n` is a nonsingular Jacobian representative of `[n]P` for every `n ≥ 0`. -/
theorem jac_spec {x y : K} (h : (WA A).toAffine.Nonsingular x y) (n : ℕ) :
    (WA A).toJacobian.Nonsingular (jac A x y n) ∧
      Point.toAffine (WA A).toJacobian (jac A x y n) = n • Affine.Point.some x y h := by
  have h2 : IsUnit (2 : K) := two_ne_zero.isUnit
  have h8 : IsUnit (8 : K) := (by norm_num : (8 : K) ≠ 0).isUnit
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [mul_zero, Nat.cast_zero, jac_zero, zero_nsmul]
      exact ⟨(nonsingular_smul _ h2).mpr nonsingular_zero,
        by rw [Point.toAffine_smul _ h2, Point.toAffine_zero]⟩
    · obtain ⟨ns, e⟩ := ih k (by omega)
      obtain ⟨hD, -⟩ := jac_identities A h.1 k hk
      have hD' := nonsingular_add ns ns
      rw [add_self, hD] at hD'
      push_cast
      refine ⟨(nonsingular_smul _ h8).mp hD', ?_⟩
      rw [← Point.toAffine_smul _ h8, ← hD, ← add_self, Point.toAffine_add ns ns, e, ← add_nsmul,
        two_mul]
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [mul_zero, zero_add, Nat.cast_one, jac_one, one_nsmul]
      have hs : (WA A).toJacobian.Nonsingular ![x, y, 1] := (nonsingular_some x y).mpr h
      exact ⟨(nonsingular_smul _ h2).mpr hs, by rw [Point.toAffine_smul _ h2, Point.toAffine_some hs]⟩
    · obtain ⟨ns, e⟩ := ih k (by omega)
      obtain ⟨ns1, e1⟩ := ih (k + 1) (by omega)
      push_cast at ns1 e1
      obtain ⟨-, hS⟩ := jac_identities A h.1 k hk
      have hne : ¬ jac A x y (k + 1) ≈ jac A x y k := by
        intro hc
        have := Point.toAffine_of_equiv (W := (WA A).toJacobian) hc
        rw [e1, e, succ_nsmul, add_eq_left] at this
        exact Affine.Point.some_ne_zero h this
      have h8' : IsUnit (-8 : K) := (by norm_num : (-8 : K) ≠ 0).isUnit
      have hS' := nonsingular_add ns1 ns
      rw [add_of_not_equiv hne, hS] at hS'
      push_cast
      refine ⟨(nonsingular_smul _ h8').mp hS', ?_⟩
      rw [← Point.toAffine_smul _ h8', ← hS, ← add_of_not_equiv hne, Point.toAffine_add ns1 ns, e1,
        e, ← add_nsmul]
      congr 1
      ring

/-- The multiplication formulas for `n ≥ 0`, in terms of the normalized EDS `w`. -/
theorem nsmul_spec {x y : K} (h : (WA A).toAffine.Nonsingular x y) (n : ℕ) :
    (n • Affine.Point.some x y h = 0 ↔ w A x y n = 0) ∧
      (w A x y n ≠ 0 →
        ∃ h', n • Affine.Point.some x y h = Affine.Point.some (xmul A x y n) (ymul A x y n) h') := by
  obtain ⟨ns, e⟩ := jac_spec h n
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun hn => ?_⟩
  · by_contra hn
    have hz : jac A x y n Z ≠ 0 := mul_ne_zero h2 hn
    rw [← e, Point.toAffine_of_Z_ne_zero ns hz] at h0
    exact Affine.Point.some_ne_zero _ h0
  · have hz : jac A x y n Z = 0 := by rw [jac_Z, h0, mul_zero]
    rw [← e, Point.toAffine_of_Z_eq_zero hz]
  · have hz : jac A x y n Z ≠ 0 := mul_ne_zero h2 hn
    have h' := (nonsingular_of_Z_ne_zero hz).mp ns
    rw [jac_div_X h2 hn, jac_div_Y h2 hn] at h'
    refine ⟨h', ?_⟩
    rw [← e, Point.toAffine_of_Z_ne_zero ns hz]
    simp only [jac_div_X h2 hn, jac_div_Y h2 hn]

/-- **Division polynomials compute multiples.** For an affine point `P = (x, y)` of
`y² = x³ + Ax` over a field of characteristic zero and every `n ∈ ℤ`: `[n]P = O` iff
`ψ_n(P) = 0`, and if `ψ_n(P) ≠ 0` then `[n]P = (x - ψ_{n+1}ψ_{n-1}/ψ_n², ψ_{2n}/(2ψ_n⁴))`. -/
theorem zsmul_spec {x y : K} (h : (WA A).toAffine.Nonsingular x y) (n : ℤ) :
    (n • Affine.Point.some x y h = 0 ↔ psiEval A n x y = 0) ∧
      (psiEval A n x y ≠ 0 →
        ∃ h' : (WA A).toAffine.Nonsingular
            (x - psiEval A (n + 1) x y * psiEval A (n - 1) x y / psiEval A n x y ^ 2)
            (psiEval A (2 * n) x y / (2 * psiEval A n x y ^ 4)),
          n • Affine.Point.some x y h = Affine.Point.some _ _ h') := by
  have hy := WA_equation_iff.mp h.1
  rw [psiEval_eq_w hy n, psiEval_eq_w hy (n + 1), psiEval_eq_w hy (n - 1),
    psiEval_eq_w hy (2 * n)]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · obtain ⟨h1, h2⟩ := nsmul_spec h k
    rw [natCast_zsmul]
    exact ⟨h1, fun hn => h2 hn⟩
  · obtain ⟨h1, h2⟩ := nsmul_spec h k
    refine ⟨by rw [neg_zsmul, natCast_zsmul, neg_eq_zero, w_neg, neg_eq_zero, h1], fun hn => ?_⟩
    have hn' : w A x y k ≠ 0 := by rwa [w_neg, neg_ne_zero] at hn
    obtain ⟨h', e⟩ := h2 hn'
    have ex : x - w A x y (-(k : ℤ) + 1) * w A x y (-(k : ℤ) - 1) / w A x y (-(k : ℤ)) ^ 2 =
        xmul A x y k := by
      rw [show -(k : ℤ) + 1 = -((k : ℤ) - 1) by ring, show -(k : ℤ) - 1 = -((k : ℤ) + 1) by ring,
        w_neg, w_neg, w_neg, xmul]
      ring
    have ey : w A x y (2 * -(k : ℤ)) / (2 * w A x y (-(k : ℤ)) ^ 4) = -ymul A x y k := by
      rw [show 2 * -(k : ℤ) = -(2 * (k : ℤ)) by ring, w_neg, w_neg, ymul]
      ring
    have h'' : (WA A).toAffine.Nonsingular (xmul A x y k) (-ymul A x y k) := by
      have := (Affine.nonsingular_neg (W' := (WA A).toAffine) _ _).mpr h'
      rwa [WA_negY] at this
    rw [ex, ey]
    refine ⟨h'', ?_⟩
    rw [neg_zsmul, natCast_zsmul, e, Affine.Point.neg_some]
    simp only [WA_negY]

end ZInQ.DivisionPolynomials
