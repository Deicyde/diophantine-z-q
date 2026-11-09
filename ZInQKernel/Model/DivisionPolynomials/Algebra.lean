import Mathlib

/-!
# Field identities for the doubling steps

Pure field computations used in the induction computing `x([n]P)`: the even step
(`x(2Q)` from `x(Q)`, `x(Q ± P)`) and the odd step (`x(U + V)` from `x(U)`, `x(V)`,
`x(U - V)`, `x(U + P)`, `x(V - P)` with `P = U - V`), for the curve `y² = x³ + Ax`.
All quantities are atoms; the hypotheses `dE`, `dO`, `dx` are the division-polynomial
recurrences rewritten as statements about differences of abscissas.
-/

namespace ZInQ.DivisionPolynomials

variable {F : Type*} [Field F]

/-- The even step. `a = x(Q)`, `Xp = x(Q + P)`, `Xm = x(Q - P)`, `x5 = x(2Q)`, `c = x(P)`. -/
lemma even_step_alg (h2 : (2 : F) ≠ 0) {A c y a y0 Xp Xm x5 W0 Wp Wm W2 W2p W2m : F}
    (hy : y ^ 2 = c ^ 3 + A * c) (hy0 : y0 ^ 2 = a ^ 3 + A * a) (hyne : y ≠ 0) (hy0ne : y0 ≠ 0)
    (hac : a - c ≠ 0) (hWp : Wp ≠ 0) (hWm : Wm ≠ 0) (hW2 : W2 ≠ 0)
    (Hs : (Xp + Xm) * (a - c) ^ 2 = 2 * (a * c + A) * (a + c))
    (Hp : Xp * Xm * (a - c) ^ 2 = (a * c - A) ^ 2)
    (Hdbl : x5 * (4 * y0 ^ 2) = (a ^ 2 - A) ^ 2)
    (dE : (Xp - Xm) * (Wp ^ 2 * Wm ^ 2) = -(2 * y) * W2)
    (dO1 : (a - Xp) * (Wp ^ 2 * W0 ^ 2) = W2p)
    (dO2 : (a - Xm) * (W0 ^ 2 * Wm ^ 2) = -W2m)
    (dx : (a - c) * W0 ^ 2 = -(Wp * Wm)) :
    x5 = c - W2p * W2m / W2 ^ 2 := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hS : Xp + Xm = 2 * (a * c + A) * (a + c) / (a - c) ^ 2 := by
    field_simp; linear_combination Hs
  have hP : Xp * Xm = (a * c - A) ^ 2 / (a - c) ^ 2 := by
    field_simp; linear_combination Hp
  have hden : a ^ 3 + A * a ≠ 0 := by rw [← hy0]; exact pow_ne_zero 2 hy0ne
  have h5 : x5 = (a ^ 2 - A) ^ 2 / (4 * (a ^ 3 + A * a)) := by
    rw [eq_div_iff (mul_ne_zero h4 hden)]; linear_combination Hdbl - 4 * x5 * hy0
  have key : (x5 - c) * (Xp - Xm) ^ 2 * (a - c) ^ 2 = 4 * y ^ 2 * (a - Xp) * (a - Xm) := by
    rw [show (Xp - Xm) ^ 2 = (Xp + Xm) ^ 2 - 4 * (Xp * Xm) by ring,
      show 4 * y ^ 2 * (a - Xp) * (a - Xm) = 4 * y ^ 2 * (a ^ 2 - a * (Xp + Xm) + Xp * Xm) by ring,
      hS, hP, h5, hy]
    have hfac : a * (a ^ 2 + A) ≠ 0 := by rwa [show a * (a ^ 2 + A) = a ^ 3 + A * a by ring]
    have ha := left_ne_zero_of_mul hfac
    have ha2 := right_ne_zero_of_mul hfac
    field_simp
    ring
  have E1 : (x5 - c) * ((Xp - Xm) * (Wp ^ 2 * Wm ^ 2)) ^ 2 * ((a - c) * W0 ^ 2) ^ 2 =
      4 * y ^ 2 * ((a - Xp) * (Wp ^ 2 * W0 ^ 2)) * ((a - Xm) * (W0 ^ 2 * Wm ^ 2)) *
        (Wp ^ 2 * Wm ^ 2) := by
    linear_combination (Wp ^ 4 * Wm ^ 4 * W0 ^ 4) * key
  rw [dE, dO1, dO2, dx] at E1
  have hne : 4 * y ^ 2 * (Wp ^ 2 * Wm ^ 2) ≠ 0 := by
    apply_rules [mul_ne_zero, pow_ne_zero]
  have E2 : (x5 - c) * W2 ^ 2 = -(W2p * W2m) :=
    mul_right_cancel₀ hne (by linear_combination E1)
  field_simp
  linear_combination E2

/-- The odd step. `a = x(U)`, `b = x(V)`, `c = x(U - V)`, `x6 = x(U + V)`, `Xp2 = x(U + P)`,
`Xm1 = x(V - P)` with `P = U - V`. -/
lemma odd_step_alg (h2 : (2 : F) ≠ 0) {A c y a b Xp2 Xm1 x6 W0 Wp Wp2 Wm W2p W2m W2pp : F}
    (hy : y ^ 2 = c ^ 3 + A * c) (hyne : y ≠ 0)
    (hWp : Wp ≠ 0) (hW0 : W0 ≠ 0) (hWp2 : Wp2 ≠ 0) (hWm : Wm ≠ 0)
    (hW2p : W2p ≠ 0)
    (Hs1 : (x6 + c) * (a - b) ^ 2 = 2 * (a * b + A) * (a + b))
    (Hp1 : x6 * c * (a - b) ^ 2 = (a * b - A) ^ 2)
    (Hs2 : (Xp2 + b) * (a - c) ^ 2 = 2 * (a * c + A) * (a + c))
    (Hs3 : (a + Xm1) * (b - c) ^ 2 = 2 * (b * c + A) * (b + c))
    (dE1 : (Xp2 - b) * (Wp2 ^ 2 * W0 ^ 2) = -(2 * y) * W2pp)
    (dE2 : (a - Xm1) * (Wp ^ 2 * Wm ^ 2) = -(2 * y) * W2m)
    (dO : (b - a) * (Wp ^ 2 * W0 ^ 2) = W2p)
    (dxa : (a - c) * Wp ^ 2 = -(Wp2 * W0))
    (dxb : (b - c) * W0 ^ 2 = -(Wp * Wm)) :
    x6 = c - W2pp * W2m / W2p ^ 2 := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hK : (a - b) ^ 2 * c ^ 2 - 2 * (a * b + A) * (a + b) * c + (a * b - A) ^ 2 = 0 := by
    linear_combination c * Hs1 - Hp1
  have key : (x6 - c) * (4 * y ^ 2) * (a - b) ^ 2 =
      -((Xp2 - b) * (a - c) ^ 2) * ((a - Xm1) * (b - c) ^ 2) := by
    linear_combination 4 * y ^ 2 * Hs1 + ((a - Xm1) * (b - c) ^ 2) * Hs2 -
      (2 * (a * c + A) * (a + c) - 2 * b * (a - c) ^ 2) * Hs3 +
      4 * (2 * (a * b + A) * (a + b) - 2 * c * (a - b) ^ 2) * hy - 4 * (a - c) * (b - c) * hK
  have E1 : (x6 - c) * (4 * y ^ 2) * ((b - a) * (Wp ^ 2 * W0 ^ 2)) ^ 2 *
      (Wp2 ^ 2 * Wm ^ 2 * (Wp ^ 2 * W0 ^ 2)) =
      -((Xp2 - b) * (Wp2 ^ 2 * W0 ^ 2)) * ((a - Xm1) * (Wp ^ 2 * Wm ^ 2)) *
        ((a - c) * Wp ^ 2) ^ 2 * ((b - c) * W0 ^ 2) ^ 2 := by
    linear_combination (Wp ^ 6 * W0 ^ 6 * Wp2 ^ 2 * Wm ^ 2) * key
  rw [dE1, dE2, dO, dxa, dxb] at E1
  have hne : 4 * y ^ 2 * (Wp2 ^ 2 * Wm ^ 2 * (Wp ^ 2 * W0 ^ 2)) ≠ 0 := by
    apply_rules [mul_ne_zero, pow_ne_zero]
  have E2 : (x6 - c) * W2p ^ 2 = -(W2pp * W2m) :=
    mul_right_cancel₀ hne (by linear_combination E1)
  field_simp
  linear_combination E2

/-- The case `n = 2`: `x(2P) = x - f₃/(2y)²`. -/
lemma base2_alg (h2 : (2 : F) ≠ 0) {A x y x5 : F} (hy : y ^ 2 = x ^ 3 + A * x) (hyne : y ≠ 0)
    (Hd : x5 * (4 * y ^ 2) = (x ^ 2 - A) ^ 2) :
    x5 = x - (3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2) * 1 / (2 * y) ^ 2 := by
  have h : (x5 - x) * (2 * y) ^ 2 = -(3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2) := by
    linear_combination Hd + (-4 * x) * hy
  have : (2 * y) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero h2 hyne)
  rw [mul_one, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff this]
  linear_combination h

/-- The case `n = 3`: `x(3P) = x - ψ₄ψ₂/ψ₃²` from `x(2P) = X2` and the chord through `2P`, `P`. -/
lemma base3_alg {A x y x3 X2 : F} (hy : y ^ 2 = x ^ 3 + A * x)
    (hf3 : 3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2 ≠ 0)
    (Hs : (x3 + x) * (X2 - x) ^ 2 = 2 * (X2 * x + A) * (X2 + x))
    (hX : (X2 - x) * (2 * y) ^ 2 = -((3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2) * 1)) :
    x3 = x - 2 * (x ^ 6 + 5 * A * x ^ 4 - 5 * A ^ 2 * x ^ 2 - A ^ 3) * (2 * y) * (2 * y) /
      (3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2) ^ 2 := by
  have T : (x3 - x) * (3 * x ^ 4 + 6 * A * x ^ 2 - A ^ 2) ^ 2 +
      4 * y ^ 2 * (2 * (x ^ 6 + 5 * A * x ^ 4 - 5 * A ^ 2 * x ^ 2 - A ^ 3)) = 0 := by
    linear_combination (4 * y ^ 2) ^ 2 * Hs +
      (A ^ 2 * x - A ^ 2 * x3 - 6 * A * x ^ 3 + 6 * A * x ^ 2 * x3 + 8 * A * y ^ 2 +
        4 * X2 * x * y ^ 2 - 4 * X2 * x3 * y ^ 2 - 3 * x ^ 5 + 3 * x ^ 4 * x3 + 20 * x ^ 2 * y ^ 2 +
        4 * x * x3 * y ^ 2) * hX + 64 * x * y ^ 2 * (A + x ^ 2) * hy
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hf3)]
  linear_combination T

/-- The ordinate: `y(nP) = ψ_{2n}/(2ψ_n⁴)` from `x((n ± 1)P)` and `x(nP)`. -/
lemma y_alg (h2 : (2 : F) ≠ 0) {y y0 a c Xp Xm W0 Wp Wm W2 : F} (hyne : y ≠ 0) (hWp : Wp ≠ 0)
    (hWm : Wm ≠ 0) (hW0 : W0 ≠ 0)
    (Hd : (Xp - Xm) * (a - c) ^ 2 = -4 * y0 * y)
    (dE : (Xp - Xm) * (Wp ^ 2 * Wm ^ 2) = -(2 * y) * W2)
    (dx : (a - c) * W0 ^ 2 = -(Wp * Wm)) :
    y0 = W2 / (2 * W0 ^ 4) := by
  have E1 : (Xp - Xm) * (Wp ^ 2 * Wm ^ 2) * ((a - c) * W0 ^ 2) ^ 2 =
      -4 * y0 * y * (Wp ^ 2 * Wm ^ 2) * W0 ^ 4 := by
    linear_combination (Wp ^ 2 * Wm ^ 2 * W0 ^ 4) * Hd
  rw [dE, dx] at E1
  have hne : -(2 * y) * (Wp ^ 2 * Wm ^ 2) ≠ 0 := by
    apply_rules [mul_ne_zero, pow_ne_zero, neg_ne_zero.mpr]
  have E2 : W2 = 2 * y0 * W0 ^ 4 := mul_right_cancel₀ hne (by linear_combination E1)
  rw [E2]
  field_simp

end ZInQ.DivisionPolynomials
