import ZInQKernel.Model.DivisionPolynomials.Geometry
import ZInQKernel.Model.DivisionPolynomials.Algebra

/-!
# Multiples of a point at which no division polynomial vanishes

For an affine point `P = (x, y)` of `y² = x³ + Ax` over a field of characteristic `≠ 2` such that
`ψ_n(P) ≠ 0` for every `n ≠ 0`, we show `[n]P = (x - ψ_{n+1}ψ_{n-1}/ψ_n², ψ_{2n}/(2ψ_n⁴))` for
`n ≥ 1`. The abscissas are computed by strong induction (`n = 2m` from `m - 1, m, m + 1` by the
duplication formula; `n = 2m + 1` from `m - 1, …, m + 2` by the chord through `[m + 1]P` and
`[m]P`), using that the defining recurrences of `ψ` are relations between differences of
abscissas. The ordinate then follows from `x(Q + P) - x(Q - P) = -4y(Q)y(P)/(x(Q) - x(P))²`.

This is applied at the generic point of the curve (see `Generic.lean`), where all `ψ_n` are
nonzero, to obtain polynomial identities valid at every point.
-/

namespace ZInQ.DivisionPolynomials

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open ZInQ.Syntax (WA divF3 divF4)

section CommRing

variable {R : Type*} [CommRing R]

/-- The values `ψ_n(x, y)`, as Mathlib's normalized elliptic divisibility sequence with
`ψ₂ = 2y`, `ψ₃ = f₃(x)`, `ψ₄ = f₄(x) · 2y`. -/
noncomputable def w (A x y : R) (n : ℤ) : R :=
  normEDS (2 * y) ((divF3 A).eval x) ((divF4 A).eval x) n

section w

variable (A x y : R)

@[simp] lemma w_zero : w A x y 0 = 0 := normEDS_zero ..
@[simp] lemma w_one : w A x y 1 = 1 := normEDS_one ..
@[simp] lemma w_two : w A x y 2 = 2 * y := normEDS_two ..
lemma w_three : w A x y 3 = 3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2 := by
  simp [w, divF3]
lemma w_four : w A x y 4 = 2 * (x ^ 6 + 5 * A * x ^ 4 - 5 * A ^ 2 * x ^ 2 - A ^ 3) * (2 * y) := by
  simp [w, divF4]
lemma w_neg (n : ℤ) : w A x y (-n) = -w A x y n := normEDS_neg ..
lemma w_even (m : ℤ) : w A x y (2 * m) * (2 * y) =
    w A x y (m - 1) ^ 2 * w A x y m * w A x y (m + 2) -
      w A x y (m - 2) * w A x y m * w A x y (m + 1) ^ 2 := normEDS_even ..
lemma w_odd (m : ℤ) : w A x y (2 * m + 1) =
    w A x y (m + 2) * w A x y m ^ 3 - w A x y (m - 1) * w A x y (m + 1) ^ 3 := normEDS_odd ..

end w

end CommRing

variable {F : Type*} [Field F]

/-- The candidate abscissa `x - ψ_{n+1}ψ_{n-1}/ψ_n²` of `[n]P`. -/
noncomputable def xmul (A x y : F) (n : ℤ) : F :=
  x - w A x y (n + 1) * w A x y (n - 1) / w A x y n ^ 2

/-- The candidate ordinate `ψ_{2n}/(2ψ_n⁴)` of `[n]P`. -/
noncomputable def ymul (A x y : F) (n : ℤ) : F :=
  w A x y (2 * n) / (2 * w A x y n ^ 4)


section rel

variable {A x y : F}

lemma dx_rel {i ip im : ℤ} (hip : ip = i + 1) (him : im = i - 1) (hi : w A x y i ≠ 0) :
    (xmul A x y i - x) * w A x y i ^ 2 = -(w A x y ip * w A x y im) := by
  subst hip him
  simp only [xmul]
  field_simp
  ring

lemma dE_rel {i ip im k : ℤ} (hip : ip = i + 1) (him : im = i - 1) (hk : k = 2 * i)
    (hp : w A x y ip ≠ 0) (hm : w A x y im ≠ 0) :
    (xmul A x y ip - xmul A x y im) * (w A x y ip ^ 2 * w A x y im ^ 2) = -(2 * y) * w A x y k := by
  subst hip him hk
  have e := w_even A x y i
  have h : (xmul A x y (i + 1) - xmul A x y (i - 1)) * (w A x y (i + 1) ^ 2 * w A x y (i - 1) ^ 2) =
      -(w A x y (i + 2) * w A x y i * w A x y (i - 1) ^ 2) +
        w A x y i * w A x y (i - 2) * w A x y (i + 1) ^ 2 := by
    simp only [xmul, show i + 1 + 1 = i + 2 by ring, show i + 1 - 1 = i by ring,
      show i - 1 + 1 = i by ring, show i - 1 - 1 = i - 2 by ring]
    field_simp
    ring
  linear_combination h + e

lemma dO_rel {i j k : ℤ} (hj : j = i + 1) (hk : k = 2 * i + 1)
    (hj0 : w A x y j ≠ 0) (hi0 : w A x y i ≠ 0) :
    (xmul A x y i - xmul A x y j) * (w A x y j ^ 2 * w A x y i ^ 2) = w A x y k := by
  subst hj hk
  have e := w_odd A x y i
  have h : (xmul A x y i - xmul A x y (i + 1)) * (w A x y (i + 1) ^ 2 * w A x y i ^ 2) =
      -(w A x y (i + 1) * w A x y (i - 1) * w A x y (i + 1) ^ 2) +
        w A x y (i + 2) * w A x y i * w A x y i ^ 2 := by
    simp only [xmul, show i + 1 + 1 = i + 2 by ring, show i + 1 - 1 = i by ring]
    field_simp
    ring
  linear_combination h - e

end rel

variable [DecidableEq F] {A : F}

lemma nsmul_sub_one (Q : (WA A).toAffine.Point) {m : ℕ} (hm : 1 ≤ m) :
    m • Q - Q = (m - 1 : ℕ) • Q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp [succ_nsmul]

/-- Abscissas of multiples of a point at which no `ψ_n` (`n ≠ 0`) vanishes. -/
theorem exists_nsmul_eq_xmul (h2 : (2 : F) ≠ 0) {x y : F} (h : (WA A).toAffine.Nonsingular x y)
    (hw : ∀ n : ℤ, n ≠ 0 → w A x y n ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ y' h', n • Point.some x y h = Point.some (xmul A x y n) y' h' := by
  have hy := WA_equation_iff.mp h.1
  have hyne : y ≠ 0 := by
    have := hw 2 (by norm_num); rw [w_two] at this; exact right_ne_zero_of_mul this
  have hw3 := hw 3 (by norm_num)
  rw [w_three] at hw3
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
    · -- n = 2
      obtain ⟨x5, y5, h5, e5⟩ := exists_add_self_of_Y_ne h2 (h₁ := h) hyne
      have Hd := dbl_rel h2 hyne e5
      have hx5 : x5 = xmul A x y ((2 * 1 : ℕ) : ℤ) := by
        simp only [xmul]; norm_num [w_three]
        simpa using base2_alg h2 hy hyne Hd
      subst hx5
      exact ⟨y5, h5, by rw [← e5, mul_one, two_nsmul]⟩
    · -- n = 2m, m ≥ 2
      obtain ⟨y0, h0, e0⟩ := ih m (by omega) (by omega)
      obtain ⟨yp, hp, ep⟩ := ih (m + 1) (by omega) (by omega)
      obtain ⟨ym, hm', em⟩ := ih (m - 1) (by omega) (by omega)
      have hWp := hw ((m + 1 : ℕ) : ℤ) (by omega)
      have hWm := hw ((m - 1 : ℕ) : ℤ) (by omega)
      have hW0 := hw (m : ℤ) (by omega)
      have hW2 := hw ((2 * m : ℕ) : ℤ) (by omega)
      have dx := dx_rel (A := A) (x := x) (y := y) (i := (m : ℤ)) (ip := ((m + 1 : ℕ) : ℤ))
        (im := ((m - 1 : ℕ) : ℤ)) (by omega) (by omega) hW0
      have hx : xmul A x y m ≠ x := by
        intro hc; rw [hc, sub_self, zero_mul] at dx
        exact mul_ne_zero hWp hWm (neg_eq_zero.mp dx.symm)
      have hadd : Point.some _ _ h0 + Point.some _ _ h = Point.some _ _ hp := by
        rw [← e0, ← ep, succ_nsmul]
      have hsub : Point.some _ _ h0 - Point.some _ _ h = Point.some _ _ hm' := by
        rw [← e0, ← em, nsmul_sub_one _ (by omega)]
      obtain ⟨Hs, Hp, Hd⟩ := chord_rel hx hadd hsub
      have dE := dE_rel (A := A) (x := x) (y := y) (i := (m : ℤ)) (ip := ((m + 1 : ℕ) : ℤ))
        (im := ((m - 1 : ℕ) : ℤ)) (k := ((2 * m : ℕ) : ℤ)) (by omega) (by omega) (by omega) hWp hWm
      have hy0ne : y0 ≠ 0 := by
        intro hc
        rw [hc] at Hd
        have h1 : xmul A x y ((m + 1 : ℕ) : ℤ) - xmul A x y ((m - 1 : ℕ) : ℤ) = 0 :=
          (mul_eq_zero.mp (by linear_combination Hd :
            (xmul A x y ((m + 1 : ℕ) : ℤ) - xmul A x y ((m - 1 : ℕ) : ℤ)) *
              (xmul A x y m - x) ^ 2 = 0)).resolve_right (pow_ne_zero 2 (sub_ne_zero.mpr hx))
        rw [h1, zero_mul] at dE
        exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero h2 hyne)) hW2 dE.symm
      obtain ⟨x5, y5, h5, e5⟩ := exists_add_self_of_Y_ne h2 (h₁ := h0) hy0ne
      have Hdbl := dbl_rel h2 hy0ne e5
      have dO1 := dO_rel (A := A) (x := x) (y := y) (i := (m : ℤ)) (j := ((m + 1 : ℕ) : ℤ))
        (k := ((2 * m : ℕ) : ℤ) + 1) (by omega) (by omega) hWp hW0
      have dO2' := dO_rel (A := A) (x := x) (y := y) (i := ((m - 1 : ℕ) : ℤ)) (j := (m : ℤ))
        (k := ((2 * m : ℕ) : ℤ) - 1) (by omega) (by omega) hW0 hWm
      have dO2 : (xmul A x y m - xmul A x y ((m - 1 : ℕ) : ℤ)) *
          (w A x y m ^ 2 * w A x y ((m - 1 : ℕ) : ℤ) ^ 2) = -w A x y (((2 * m : ℕ) : ℤ) - 1) := by
        linear_combination -dO2'
      have hx5 : x5 = xmul A x y ((2 * m : ℕ) : ℤ) :=
        even_step_alg h2 hy (WA_equation_iff.mp h0.1) hyne hy0ne (sub_ne_zero.mpr hx) hWp hWm hW2
          Hs Hp Hdbl dE dO1 dO2 dx
      subst hx5
      exact ⟨y5, h5, by rw [← e5, ← e0, two_mul, add_nsmul]⟩
  · rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
    · -- n = 1
      have : xmul A x y ((2 * 0 + 1 : ℕ) : ℤ) = x := by simp [xmul]
      rw [this]
      exact ⟨y, h, by simp⟩
    · -- n = 3
      obtain ⟨y2, h2', e2⟩ := ih 2 (by omega) (by omega)
      have dx2 := dx_rel (A := A) (x := x) (y := y) (i := ((2 : ℕ) : ℤ)) (ip := 3) (im := 1)
        (by norm_num) (by norm_num) (hw _ (by norm_num))
      have hx : xmul A x y ((2 : ℕ) : ℤ) ≠ x := by
        intro hc; rw [hc, sub_self, zero_mul] at dx2
        rw [w_three, w_one] at dx2
        exact hw3 (by linear_combination dx2)
      obtain ⟨x3, y3, h3, e3⟩ := exists_add_of_X_ne (h₁ := h2') (h₂ := h) hx
      have hsub : Point.some _ _ h2' - Point.some _ _ h = Point.some _ _ h := by
        rw [← e2, two_nsmul, add_sub_cancel_right]
      obtain ⟨Hs, -, -⟩ := chord_rel hx e3 hsub
      have hX : (xmul A x y ((2 : ℕ) : ℤ) - x) * (2 * y) ^ 2 =
          -((3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2) * 1) := by
        rw [← w_three, ← w_one A x y, ← w_two A x y]; exact_mod_cast dx2
      have hx3 : x3 = xmul A x y ((2 * 1 + 1 : ℕ) : ℤ) := by
        rw [base3_alg hy hw3 Hs hX]
        simp only [xmul]; norm_num [w_four, w_three]
      subst hx3
      exact ⟨y3, h3, by rw [← e3, ← e2, show 2 * 1 + 1 = 2 + 1 by rfl, succ_nsmul]⟩
    · -- n = 2m + 1, m ≥ 2
      obtain ⟨y2, h2', e2⟩ := ih (m + 2) (by omega) (by omega)
      obtain ⟨yU, hU, eU⟩ := ih (m + 1) (by omega) (by omega)
      obtain ⟨yV, hV, eV⟩ := ih m (by omega) (by omega)
      obtain ⟨ym, hm', em⟩ := ih (m - 1) (by omega) (by omega)
      have hWp2 := hw ((m + 2 : ℕ) : ℤ) (by omega)
      have hWp := hw ((m + 1 : ℕ) : ℤ) (by omega)
      have hW0 := hw (m : ℤ) (by omega)
      have hWm := hw ((m - 1 : ℕ) : ℤ) (by omega)
      have hW2p := hw ((2 * m + 1 : ℕ) : ℤ) (by omega)
      have dO := dO_rel (A := A) (x := x) (y := y) (i := (m : ℤ)) (j := ((m + 1 : ℕ) : ℤ))
        (k := ((2 * m + 1 : ℕ) : ℤ)) (by omega) (by omega) hWp hW0
      have hab : xmul A x y ((m + 1 : ℕ) : ℤ) ≠ xmul A x y m := by
        intro hc; rw [hc, sub_self, zero_mul] at dO; exact hW2p dO.symm
      obtain ⟨x6, y6, h6, e6⟩ := exists_add_of_X_ne (h₁ := hU) (h₂ := hV) hab
      have hsub1 : Point.some _ _ hU - Point.some _ _ hV = Point.some _ _ h := by
        rw [← eU, ← eV, succ_nsmul, add_sub_cancel_left]
      obtain ⟨Hs1, Hp1, -⟩ := chord_rel hab e6 hsub1
      have dxa := dx_rel (A := A) (x := x) (y := y) (i := ((m + 1 : ℕ) : ℤ))
        (ip := ((m + 2 : ℕ) : ℤ)) (im := (m : ℤ)) (by omega) (by omega) hWp
      have hax : xmul A x y ((m + 1 : ℕ) : ℤ) ≠ x := by
        intro hc; rw [hc, sub_self, zero_mul] at dxa
        exact mul_ne_zero hWp2 hW0 (neg_eq_zero.mp dxa.symm)
      have hadd2 : Point.some _ _ hU + Point.some _ _ h = Point.some _ _ h2' := by
        rw [← eU, ← e2, show m + 2 = m + 1 + 1 by ring, succ_nsmul _ (m + 1)]
      have hsub2 : Point.some _ _ hU - Point.some _ _ h = Point.some _ _ hV := by
        rw [← eU, ← eV, succ_nsmul, add_sub_cancel_right]
      obtain ⟨Hs2, -, -⟩ := chord_rel hax hadd2 hsub2
      have dxb := dx_rel (A := A) (x := x) (y := y) (i := (m : ℤ)) (ip := ((m + 1 : ℕ) : ℤ))
        (im := ((m - 1 : ℕ) : ℤ)) (by omega) (by omega) hW0
      have hbx : xmul A x y m ≠ x := by
        intro hc; rw [hc, sub_self, zero_mul] at dxb
        exact mul_ne_zero hWp hWm (neg_eq_zero.mp dxb.symm)
      have hadd3 : Point.some _ _ hV + Point.some _ _ h = Point.some _ _ hU := by
        rw [← eV, ← eU, succ_nsmul]
      have hsub3 : Point.some _ _ hV - Point.some _ _ h = Point.some _ _ hm' := by
        rw [← eV, ← em, nsmul_sub_one _ (by omega)]
      obtain ⟨Hs3, -, -⟩ := chord_rel hbx hadd3 hsub3
      have dE1 := dE_rel (A := A) (x := x) (y := y) (i := ((m + 1 : ℕ) : ℤ))
        (ip := ((m + 2 : ℕ) : ℤ)) (im := (m : ℤ)) (k := ((2 * m + 1 : ℕ) : ℤ) + 1)
        (by omega) (by omega) (by omega) hWp2 hW0
      have dE2 := dE_rel (A := A) (x := x) (y := y) (i := (m : ℤ)) (ip := ((m + 1 : ℕ) : ℤ))
        (im := ((m - 1 : ℕ) : ℤ)) (k := ((2 * m + 1 : ℕ) : ℤ) - 1)
        (by omega) (by omega) (by omega) hWp hWm
      have hx6 : x6 = xmul A x y ((2 * m + 1 : ℕ) : ℤ) :=
        odd_step_alg h2 hy hyne hWp hW0 hWp2 hWm hW2p Hs1 Hp1 Hs2 Hs3 dE1 dE2 dO dxa dxb
      subst hx6
      exact ⟨y6, h6, by rw [← e6, ← eU, ← eV, ← add_nsmul, show m + 1 + m = 2 * m + 1 by ring]⟩

/-- **Multiples of a point at which no `ψ_n` (`n ≠ 0`) vanishes**:
`[n]P = (x - ψ_{n+1}ψ_{n-1}/ψ_n², ψ_{2n}/(2ψ_n⁴))` for `n ≥ 1`. -/
theorem exists_nsmul_eq (h2 : (2 : F) ≠ 0) {x y : F} (h : (WA A).toAffine.Nonsingular x y)
    (hw : ∀ n : ℤ, n ≠ 0 → w A x y n ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ h', n • Point.some x y h = Point.some (xmul A x y n) (ymul A x y n) h' := by
  have hyne : y ≠ 0 := by
    have := hw 2 (by norm_num); rw [w_two] at this; exact right_ne_zero_of_mul this
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · have e1 : xmul A x y ((1 : ℕ) : ℤ) = x := by simp [xmul]
    have e2 : ymul A x y ((1 : ℕ) : ℤ) = y := by
      simp only [ymul, Nat.cast_one, mul_one, w_one, w_two, one_pow]
      field_simp
    rw [e1, e2]
    exact ⟨h, one_nsmul _⟩
  · obtain ⟨y0, h0, e0⟩ := exists_nsmul_eq_xmul h2 h hw n hn
    obtain ⟨yp, hp, ep⟩ := exists_nsmul_eq_xmul h2 h hw (n + 1) (by omega)
    obtain ⟨ym, hm', em⟩ := exists_nsmul_eq_xmul h2 h hw (n - 1) (by omega)
    have hWp := hw ((n + 1 : ℕ) : ℤ) (by omega)
    have hWm := hw ((n - 1 : ℕ) : ℤ) (by omega)
    have hW0 := hw (n : ℤ) (by omega)
    have dx := dx_rel (A := A) (x := x) (y := y) (i := (n : ℤ)) (ip := ((n + 1 : ℕ) : ℤ))
      (im := ((n - 1 : ℕ) : ℤ)) (by omega) (by omega) hW0
    have hx : xmul A x y n ≠ x := by
      intro hc; rw [hc, sub_self, zero_mul] at dx
      exact mul_ne_zero hWp hWm (neg_eq_zero.mp dx.symm)
    have hadd : Point.some _ _ h0 + Point.some _ _ h = Point.some _ _ hp := by
      rw [← e0, ← ep, succ_nsmul]
    have hsub : Point.some _ _ h0 - Point.some _ _ h = Point.some _ _ hm' := by
      rw [← e0, ← em, nsmul_sub_one _ (by omega)]
    obtain ⟨-, -, Hd⟩ := chord_rel hx hadd hsub
    have dE := dE_rel (A := A) (x := x) (y := y) (i := (n : ℤ)) (ip := ((n + 1 : ℕ) : ℤ))
      (im := ((n - 1 : ℕ) : ℤ)) (k := 2 * (n : ℤ)) (by omega) (by omega) rfl hWp hWm
    have hy0 : y0 = ymul A x y n := y_alg h2 hyne hWp hWm hW0 Hd dE dx
    subst hy0
    exact ⟨h0, e0⟩

end ZInQ.DivisionPolynomials
