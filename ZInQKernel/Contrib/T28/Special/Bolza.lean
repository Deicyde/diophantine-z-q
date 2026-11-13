import ZInQKernel.Contrib.T28.Special.Family

/-!
# T28, special locus: Bolza's criterion `det yv = 0 ⇒` extra involution (task igusa-special)

For the root normal form `Nr l m n = x(x-1)(x-l)(x-m)(x-n)` (a binary sextic with roots
`∞, 0, 1, l, m, n`), Clebsch's determinant factors over the fifteen synthemes of the six roots:
`det yv (Nr l m n) = (1/384433593750) · ∏ₛ Dₛ`, where `Dₛ` is the determinant of the three
quadratics `q₁, q₂, q₃` of the syntheme `s` (`det_yv_Nr`; computed in `scratch/igusa-special/t4.py`,
proved by `ring` through the elementary symmetric functions, `det_yv_Ne`). `Dₛ = 0` says that
`q₁, q₂, q₃` lie in a pencil, i.e. a Möbius involution swaps the roots in pairs; conjugating its
fixed points to `0, ∞` makes the sextic even (`clsN_odd*`), and an even sextic with `J₁₀ ≠ 0` is
equivalent to `E a b = x⁶ + a x⁴ + b x² + 1` (`even_to_E`). Result: `special_Nr`.
The fifteen synthemes fall into four orbits under permutations of `l, m, n`:
`(∞0)(1l)(mn)`, `(∞1)(0l)(mn)`, `(∞l)(01)(mn)`, `(∞l)(0m)(1n)` (`D1 … D4`).
No `sorry`, no `axiom`.
-/

namespace T28Special
open PkgI1

/-- `x(x-1)(x³ - e₁x² + e₂x - e₃)` as a binary sextic (root at `∞`). -/
def Ne {K : Type*} [Field K] (e1 e2 e3 : K) : Fin 7 → K :=
  ![0, e3, -(e2 + e3), e1 + e2, -(1 + e1), 1, 0]

/-- `x(x-1)(x-l)(x-m)(x-n)`: the binary sextic with roots `∞, 0, 1, l, m, n`. -/
def Nr {K : Type*} [Field K] (l m n : K) : Fin 7 → K :=
  Ne (l + m + n) (l * m + l * n + m * n) (l * m * n)

theorem Nr_eq_of {K : Type*} [Field K] {l m n l' m' n' : K} (h1 : l' + m' + n' = l + m + n)
    (h2 : l' * m' + l' * n' + m' * n' = l * m + l * n + m * n) (h3 : l' * m' * n' = l * m * n) :
    Nr l' m' n' = Nr l m n := by
  unfold Nr; rw [h1, h2, h3]

/-! ## Clebsch's determinant on the normal form -/

def T1 {K : Type*} [Field K] (e1 e2 e3 : K) : K :=
    (-1 : K) * e1 ^ 2 * e3 + (-2 : K) * e1 * e3 + e2 ^ 2 + (2 : K) * e2 * e3 + e3 ^ 2 +
    (-1 : K) * e3

def T2 {K : Type*} [Field K] (e1 e2 e3 : K) : K :=
    e1 ^ 3 + (-1 : K) * e1 ^ 2 * e2 + e1 ^ 2 * e3 + (-4 : K) * e1 * e2 + (-2 : K) * e1 * e3 +
    (4 : K) * e2 ^ 2 + (-4 : K) * e2 * e3 + e3 ^ 2 + (8 : K) * e3

def T3 {K : Type*} [Field K] (e1 e2 e3 : K) : K :=
    (4 : K) * e1 ^ 2 * e3 + (-1 : K) * e1 * e2 ^ 2 + (-4 : K) * e1 * e2 * e3 + (-4 : K) * e1 * e3 +
    e2 ^ 3 + e2 ^ 2 + (-2 : K) * e2 * e3 + (8 : K) * e3 ^ 2 + e3

def T4 {K : Type*} [Field K] (e1 e2 e3 : K) : K :=
    e1 ^ 5 * e3 + (-1 : K) * e1 ^ 4 * e2 * e3 + (5 : K) * e1 ^ 4 * e3 ^ 2 + (-4 : K) * e1 ^ 4 * e3 +
    (-1 : K) * e1 ^ 3 * e2 ^ 2 * e3 + e1 ^ 3 * e2 ^ 2 + (-4 : K) * e1 ^ 3 * e2 * e3 ^ 2 +
    (-4 : K) * e1 ^ 3 * e2 * e3 + (4 : K) * e1 ^ 3 * e3 ^ 3 + (-19 : K) * e1 ^ 3 * e3 ^ 2 +
    (4 : K) * e1 ^ 3 * e3 + e1 ^ 2 * e2 ^ 3 * e3 + (-1 : K) * e1 ^ 2 * e2 ^ 3 +
    (-1 : K) * e1 ^ 2 * e2 ^ 2 * e3 ^ 2 + (16 : K) * e1 ^ 2 * e2 ^ 2 * e3 +
    (-1 : K) * e1 ^ 2 * e2 ^ 2 + (-9 : K) * e1 ^ 2 * e2 * e3 ^ 2 + (18 : K) * e1 ^ 2 * e2 * e3 +
    (27 : K) * e1 ^ 2 * e3 ^ 2 + (-1 : K) * e1 * e2 ^ 4 + (-4 : K) * e1 * e2 ^ 3 * e3 +
    (-4 : K) * e1 * e2 ^ 3 + (18 : K) * e1 * e2 ^ 2 * e3 ^ 2 + (-9 : K) * e1 * e2 ^ 2 * e3 +
    (-18 : K) * e1 * e2 * e3 ^ 3 + (18 : K) * e1 * e2 * e3 ^ 2 + (-18 : K) * e1 * e2 * e3 +
    (-27 : K) * e1 * e3 ^ 3 + (-27 : K) * e1 * e3 ^ 2 + e2 ^ 5 + (-4 : K) * e2 ^ 4 * e3 +
    (5 : K) * e2 ^ 4 + (4 : K) * e2 ^ 3 * e3 ^ 2 + (-19 : K) * e2 ^ 3 * e3 + (4 : K) * e2 ^ 3 +
    (27 : K) * e2 ^ 2 * e3 ^ 2 + (-27 : K) * e2 * e3 ^ 3 + (-27 : K) * e2 * e3 ^ 2 +
    (27 : K) * e3 ^ 4 + (54 : K) * e3 ^ 3 + (27 : K) * e3 ^ 2

set_option maxHeartbeats 4000000 in
theorem y1c0_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y1c0 (Ne e1 e2 e3) =
    ((-1 : K) / 750) * e1 ^ 2 * e2 + ((1 : K) / 1125) * e1 ^ 2 * e3 +
    ((1 : K) / 1125) * e1 * e2 ^ 2 + ((1 : K) / 150) * e1 * e2 * e3 +
    ((4 : K) / 1125) * e1 * e3 ^ 2 + ((1 : K) / 450) * e1 * e3 + ((-1 : K) / 750) * e2 ^ 3 +
    ((-1 : K) / 750) * e2 ^ 2 * e3 + ((4 : K) / 1125) * e2 ^ 2 + ((-29 : K) / 2250) * e2 * e3 +
    ((-7 : K) / 375) * e3 ^ 2 := by
  simp only [y1c0, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y1c1_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y1c1 (Ne e1 e2 e3) =
    ((1 : K) / 250) * e1 ^ 3 + ((-7 : K) / 2250) * e1 ^ 2 * e2 + ((13 : K) / 1125) * e1 ^ 2 * e3 +
    ((-7 : K) / 2250) * e1 * e2 ^ 2 + ((-17 : K) / 1125) * e1 * e2 * e3 +
    ((-17 : K) / 1125) * e1 * e2 + ((-7 : K) / 1125) * e1 * e3 + ((1 : K) / 250) * e2 ^ 3 +
    ((13 : K) / 1125) * e2 ^ 2 + ((-7 : K) / 1125) * e2 * e3 + ((2 : K) / 75) * e3 ^ 2 +
    ((2 : K) / 75) * e3 := by
  simp only [y1c1, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y1c2_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y1c2 (Ne e1 e2 e3) =
    ((-1 : K) / 750) * e1 ^ 3 + ((1 : K) / 1125) * e1 ^ 2 * e2 + ((4 : K) / 1125) * e1 ^ 2 * e3 +
    ((-1 : K) / 750) * e1 ^ 2 + ((-1 : K) / 750) * e1 * e2 ^ 2 + ((1 : K) / 150) * e1 * e2 +
    ((-29 : K) / 2250) * e1 * e3 + ((1 : K) / 1125) * e2 ^ 2 + ((1 : K) / 450) * e2 * e3 +
    ((4 : K) / 1125) * e2 + ((-7 : K) / 375) * e3 := by
  simp only [y1c2, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y2c0_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y2c0 (Ne e1 e2 e3) =
    ((1 : K) / 56250) * e1 ^ 4 * e2 + ((-1 : K) / 84375) * e1 ^ 4 * e3 +
    ((-2 : K) / 84375) * e1 ^ 3 * e2 ^ 2 + ((7 : K) / 33750) * e1 ^ 3 * e2 * e3 +
    ((-16 : K) / 28125) * e1 ^ 3 * e3 ^ 2 + ((-1 : K) / 33750) * e1 ^ 3 * e3 +
    ((-1 : K) / 28125) * e1 ^ 2 * e2 ^ 3 + ((11 : K) / 56250) * e1 ^ 2 * e2 ^ 2 * e3 +
    ((-8 : K) / 84375) * e1 ^ 2 * e2 ^ 2 + ((31 : K) / 84375) * e1 ^ 2 * e2 * e3 ^ 2 +
    ((-7 : K) / 168750) * e1 ^ 2 * e2 * e3 + ((4 : K) / 84375) * e1 ^ 2 * e3 ^ 3 +
    ((37 : K) / 84375) * e1 ^ 2 * e3 ^ 2 + ((-2 : K) / 84375) * e1 * e2 ^ 4 +
    ((-1 : K) / 6750) * e1 * e2 ^ 3 * e3 + ((4 : K) / 28125) * e1 * e2 ^ 3 +
    ((-8 : K) / 84375) * e1 * e2 ^ 2 * e3 ^ 2 + ((-19 : K) / 18750) * e1 * e2 ^ 2 * e3 +
    ((88 : K) / 84375) * e1 * e2 * e3 ^ 2 + ((7 : K) / 16875) * e1 * e2 * e3 +
    ((-8 : K) / 9375) * e1 * e3 ^ 3 + ((4 : K) / 5625) * e1 * e3 ^ 2 +
    ((1 : K) / 56250) * e2 ^ 5 + ((1 : K) / 56250) * e2 ^ 4 * e3 + ((4 : K) / 28125) * e2 ^ 4 +
    ((-17 : K) / 168750) * e2 ^ 3 * e3 + ((4 : K) / 84375) * e2 ^ 3 +
    ((2 : K) / 84375) * e2 ^ 2 * e3 ^ 2 + ((-53 : K) / 84375) * e2 ^ 2 * e3 +
    ((4 : K) / 16875) * e2 * e3 ^ 3 + ((97 : K) / 84375) * e2 * e3 ^ 2 +
    ((-32 : K) / 28125) * e3 ^ 3 + ((-1 : K) / 1125) * e3 ^ 2 := by
  simp only [y2c0, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y2c1_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y2c1 (Ne e1 e2 e3) =
    ((-1 : K) / 18750) * e1 ^ 5 + ((13 : K) / 168750) * e1 ^ 4 * e2 +
    ((-11 : K) / 84375) * e1 ^ 4 * e3 + ((1 : K) / 28125) * e1 ^ 3 * e2 * e3 +
    ((29 : K) / 84375) * e1 ^ 3 * e2 + ((38 : K) / 84375) * e1 ^ 3 * e3 ^ 2 +
    ((-1 : K) / 84375) * e1 ^ 3 * e3 + ((-37 : K) / 84375) * e1 ^ 2 * e2 ^ 2 * e3 +
    ((-37 : K) / 84375) * e1 ^ 2 * e2 ^ 2 + ((-14 : K) / 28125) * e1 ^ 2 * e2 * e3 ^ 2 +
    ((44 : K) / 84375) * e1 ^ 2 * e2 * e3 + ((-34 : K) / 84375) * e1 ^ 2 * e3 ^ 2 +
    ((-8 : K) / 16875) * e1 ^ 2 * e3 + ((13 : K) / 168750) * e1 * e2 ^ 4 +
    ((29 : K) / 84375) * e1 * e2 ^ 3 * e3 + ((1 : K) / 28125) * e1 * e2 ^ 3 +
    ((44 : K) / 84375) * e1 * e2 ^ 2 * e3 + ((-14 : K) / 28125) * e1 * e2 ^ 2 +
    ((17 : K) / 28125) * e1 * e2 * e3 ^ 2 + ((17 : K) / 28125) * e1 * e2 * e3 +
    ((16 : K) / 16875) * e1 * e3 ^ 3 + ((-77 : K) / 84375) * e1 * e3 ^ 2 +
    ((-1 : K) / 18750) * e2 ^ 5 + ((-11 : K) / 84375) * e2 ^ 4 +
    ((-1 : K) / 84375) * e2 ^ 3 * e3 + ((38 : K) / 84375) * e2 ^ 3 +
    ((-8 : K) / 16875) * e2 ^ 2 * e3 ^ 2 + ((-34 : K) / 84375) * e2 ^ 2 * e3 +
    ((-77 : K) / 84375) * e2 * e3 ^ 2 + ((16 : K) / 16875) * e2 * e3 +
    ((-1 : K) / 1875) * e3 ^ 3 + ((-1 : K) / 1875) * e3 ^ 2 := by
  simp only [y2c1, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y2c2_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y2c2 (Ne e1 e2 e3) =
    ((1 : K) / 56250) * e1 ^ 5 + ((-2 : K) / 84375) * e1 ^ 4 * e2 + ((4 : K) / 28125) * e1 ^ 4 * e3 +
    ((1 : K) / 56250) * e1 ^ 4 + ((-1 : K) / 28125) * e1 ^ 3 * e2 ^ 2 +
    ((4 : K) / 28125) * e1 ^ 3 * e2 * e3 + ((-1 : K) / 6750) * e1 ^ 3 * e2 +
    ((4 : K) / 84375) * e1 ^ 3 * e3 ^ 2 + ((-17 : K) / 168750) * e1 ^ 3 * e3 +
    ((-2 : K) / 84375) * e1 ^ 2 * e2 ^ 3 + ((-8 : K) / 84375) * e1 ^ 2 * e2 ^ 2 * e3 +
    ((11 : K) / 56250) * e1 ^ 2 * e2 ^ 2 + ((-19 : K) / 18750) * e1 ^ 2 * e2 * e3 +
    ((-8 : K) / 84375) * e1 ^ 2 * e2 + ((-53 : K) / 84375) * e1 ^ 2 * e3 ^ 2 +
    ((2 : K) / 84375) * e1 ^ 2 * e3 + ((1 : K) / 56250) * e1 * e2 ^ 4 +
    ((7 : K) / 33750) * e1 * e2 ^ 3 + ((-7 : K) / 168750) * e1 * e2 ^ 2 * e3 +
    ((31 : K) / 84375) * e1 * e2 ^ 2 + ((7 : K) / 16875) * e1 * e2 * e3 ^ 2 +
    ((88 : K) / 84375) * e1 * e2 * e3 + ((97 : K) / 84375) * e1 * e3 ^ 2 +
    ((4 : K) / 16875) * e1 * e3 + ((-1 : K) / 84375) * e2 ^ 4 +
    ((-1 : K) / 33750) * e2 ^ 3 * e3 + ((-16 : K) / 28125) * e2 ^ 3 +
    ((37 : K) / 84375) * e2 ^ 2 * e3 + ((4 : K) / 84375) * e2 ^ 2 +
    ((4 : K) / 5625) * e2 * e3 ^ 2 + ((-8 : K) / 9375) * e2 * e3 + ((-1 : K) / 1125) * e3 ^ 3 +
    ((-32 : K) / 28125) * e3 ^ 2 := by
  simp only [y2c2, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y3c0_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y3c0 (Ne e1 e2 e3) =
    ((-1 : K) / 4218750) * e1 ^ 6 * e2 + ((1 : K) / 6328125) * e1 ^ 6 * e3 +
    ((1 : K) / 2109375) * e1 ^ 5 * e2 ^ 2 + ((-1 : K) / 1265625) * e1 ^ 5 * e2 * e3 +
    ((-58 : K) / 6328125) * e1 ^ 5 * e3 ^ 2 + ((1 : K) / 2531250) * e1 ^ 5 * e3 +
    ((-1 : K) / 4218750) * e1 ^ 4 * e2 ^ 3 + ((2 : K) / 253125) * e1 ^ 4 * e2 ^ 2 * e3 +
    ((4 : K) / 2109375) * e1 ^ 4 * e2 ^ 2 + ((-47 : K) / 4218750) * e1 ^ 4 * e2 * e3 ^ 2 +
    ((-16 : K) / 6328125) * e1 ^ 4 * e2 * e3 + ((-22 : K) / 6328125) * e1 ^ 4 * e3 ^ 3 +
    ((97 : K) / 6328125) * e1 ^ 4 * e3 ^ 2 + ((-8 : K) / 6328125) * e1 ^ 3 * e2 ^ 4 +
    ((17 : K) / 4218750) * e1 ^ 3 * e2 ^ 3 * e3 + ((-7 : K) / 2109375) * e1 ^ 3 * e2 ^ 3 +
    ((59 : K) / 6328125) * e1 ^ 3 * e2 ^ 2 * e3 ^ 2 +
    ((-19 : K) / 4218750) * e1 ^ 3 * e2 ^ 2 * e3 + ((92 : K) / 6328125) * e1 ^ 3 * e2 * e3 ^ 3 +
    ((376 : K) / 6328125) * e1 ^ 3 * e2 * e3 ^ 2 + ((-13 : K) / 2531250) * e1 ^ 3 * e2 * e3 +
    ((4 : K) / 6328125) * e1 ^ 3 * e3 ^ 4 + ((196 : K) / 6328125) * e1 ^ 3 * e3 ^ 3 +
    ((7 : K) / 421875) * e1 ^ 3 * e3 ^ 2 + ((-1 : K) / 4218750) * e1 ^ 2 * e2 ^ 5 +
    ((-11 : K) / 2531250) * e1 ^ 2 * e2 ^ 4 * e3 + ((7 : K) / 2109375) * e1 ^ 2 * e2 ^ 4 +
    ((-131 : K) / 12656250) * e1 ^ 2 * e2 ^ 3 * e3 ^ 2 +
    ((-287 : K) / 6328125) * e1 ^ 2 * e2 ^ 3 * e3 + ((-1 : K) / 234375) * e1 ^ 2 * e2 ^ 3 +
    ((-1 : K) / 234375) * e1 ^ 2 * e2 ^ 2 * e3 ^ 3 +
    ((49 : K) / 2531250) * e1 ^ 2 * e2 ^ 2 * e3 ^ 2 +
    ((8 : K) / 2109375) * e1 ^ 2 * e2 ^ 2 * e3 + ((-76 : K) / 1265625) * e1 ^ 2 * e2 * e3 ^ 3 +
    ((-499 : K) / 4218750) * e1 ^ 2 * e2 * e3 ^ 2 + ((-22 : K) / 703125) * e1 ^ 2 * e3 ^ 4 +
    ((-43 : K) / 703125) * e1 ^ 2 * e3 ^ 3 + ((-1 : K) / 168750) * e1 ^ 2 * e3 ^ 2 +
    ((1 : K) / 2109375) * e1 * e2 ^ 6 + ((7 : K) / 2531250) * e1 * e2 ^ 5 * e3 +
    ((13 : K) / 2109375) * e1 * e2 ^ 5 + ((4 : K) / 2109375) * e1 * e2 ^ 4 * e3 ^ 2 +
    ((-31 : K) / 6328125) * e1 * e2 ^ 4 * e3 + ((16 : K) / 2109375) * e1 * e2 ^ 4 +
    ((151 : K) / 6328125) * e1 * e2 ^ 3 * e3 ^ 2 + ((376 : K) / 6328125) * e1 * e2 ^ 3 * e3 +
    ((49 : K) / 4218750) * e1 * e2 ^ 2 * e3 ^ 3 + ((-2 : K) / 421875) * e1 * e2 ^ 2 * e3 ^ 2 +
    ((26 : K) / 1265625) * e1 * e2 ^ 2 * e3 + ((2 : K) / 140625) * e1 * e2 * e3 ^ 4 +
    ((-737 : K) / 12656250) * e1 * e2 * e3 ^ 3 + ((-13 : K) / 1265625) * e1 * e2 * e3 ^ 2 +
    ((209 : K) / 2109375) * e1 * e3 ^ 4 + ((109 : K) / 843750) * e1 * e3 ^ 3 +
    ((-1 : K) / 4218750) * e2 ^ 7 + ((-1 : K) / 4218750) * e2 ^ 6 * e3 +
    ((-1 : K) / 2109375) * e2 ^ 6 + ((-2 : K) / 2109375) * e2 ^ 5 * e3 +
    ((-29 : K) / 2109375) * e2 ^ 5 + ((-41 : K) / 12656250) * e2 ^ 4 * e3 ^ 2 +
    ((3 : K) / 156250) * e2 ^ 4 * e3 + ((4 : K) / 6328125) * e2 ^ 4 +
    ((-1 : K) / 421875) * e2 ^ 3 * e3 ^ 3 + ((-11 : K) / 6328125) * e2 ^ 3 * e3 ^ 2 +
    ((-154 : K) / 6328125) * e2 ^ 3 * e3 + ((-167 : K) / 6328125) * e2 ^ 2 * e3 ^ 3 +
    ((-91 : K) / 6328125) * e2 ^ 2 * e3 ^ 2 + ((61 : K) / 2531250) * e2 * e3 ^ 4 +
    ((121 : K) / 6328125) * e2 * e3 ^ 3 + ((-1 : K) / 50625) * e2 * e3 ^ 2 +
    ((-2 : K) / 84375) * e3 ^ 5 + ((11 : K) / 4218750) * e3 ^ 4 + ((1 : K) / 33750) * e3 ^ 3 := by
  simp only [y3c0, y3c0_0, y3c0_1, y3c0_2, y3c0_3, y3c0_4, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y3c1_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y3c1 (Ne e1 e2 e3) =
    ((1 : K) / 1406250) * e1 ^ 7 + ((-19 : K) / 12656250) * e1 ^ 6 * e2 +
    ((1 : K) / 703125) * e1 ^ 6 * e3 + ((11 : K) / 12656250) * e1 ^ 5 * e2 ^ 2 +
    ((-28 : K) / 6328125) * e1 ^ 5 * e2 * e3 + ((-41 : K) / 6328125) * e1 ^ 5 * e2 +
    ((4 : K) / 703125) * e1 ^ 5 * e3 ^ 2 + ((1 : K) / 703125) * e1 ^ 5 * e3 +
    ((7 : K) / 12656250) * e1 ^ 4 * e2 ^ 3 + ((-4 : K) / 1265625) * e1 ^ 4 * e2 ^ 2 * e3 +
    ((77 : K) / 6328125) * e1 ^ 4 * e2 ^ 2 + ((97 : K) / 6328125) * e1 ^ 4 * e2 * e3 ^ 2 +
    ((-56 : K) / 6328125) * e1 ^ 4 * e2 * e3 + ((88 : K) / 6328125) * e1 ^ 4 * e3 ^ 3 +
    ((14 : K) / 2109375) * e1 ^ 4 * e3 ^ 2 + ((2 : K) / 253125) * e1 ^ 4 * e3 +
    ((7 : K) / 12656250) * e1 ^ 3 * e2 ^ 4 + ((-1 : K) / 140625) * e1 ^ 3 * e2 ^ 3 * e3 +
    ((-1 : K) / 140625) * e1 ^ 3 * e2 ^ 3 + ((-61 : K) / 2109375) * e1 ^ 3 * e2 ^ 2 * e3 ^ 2 +
    ((179 : K) / 6328125) * e1 ^ 3 * e2 ^ 2 * e3 + ((116 : K) / 6328125) * e1 ^ 3 * e2 ^ 2 +
    ((-92 : K) / 6328125) * e1 ^ 3 * e2 * e3 ^ 3 +
    ((-362 : K) / 6328125) * e1 ^ 3 * e2 * e3 ^ 2 + ((-133 : K) / 6328125) * e1 ^ 3 * e2 * e3 +
    ((-436 : K) / 6328125) * e1 ^ 3 * e3 ^ 3 + ((-149 : K) / 6328125) * e1 ^ 3 * e3 ^ 2 +
    ((11 : K) / 12656250) * e1 ^ 2 * e2 ^ 5 + ((77 : K) / 6328125) * e1 ^ 2 * e2 ^ 4 * e3 +
    ((-4 : K) / 1265625) * e1 ^ 2 * e2 ^ 4 + ((116 : K) / 6328125) * e1 ^ 2 * e2 ^ 3 * e3 ^ 2 +
    ((179 : K) / 6328125) * e1 ^ 2 * e2 ^ 3 * e3 + ((-61 : K) / 2109375) * e1 ^ 2 * e2 ^ 3 +
    ((178 : K) / 6328125) * e1 ^ 2 * e2 ^ 2 * e3 ^ 2 +
    ((178 : K) / 6328125) * e1 ^ 2 * e2 ^ 2 * e3 + ((434 : K) / 6328125) * e1 ^ 2 * e2 * e3 ^ 3 +
    ((-2 : K) / 140625) * e1 ^ 2 * e2 * e3 ^ 2 + ((-17 : K) / 421875) * e1 ^ 2 * e2 * e3 +
    ((4 : K) / 140625) * e1 ^ 2 * e3 ^ 4 + ((299 : K) / 6328125) * e1 ^ 2 * e3 ^ 3 +
    ((14 : K) / 1265625) * e1 ^ 2 * e3 ^ 2 + ((-19 : K) / 12656250) * e1 * e2 ^ 6 +
    ((-41 : K) / 6328125) * e1 * e2 ^ 5 * e3 + ((-28 : K) / 6328125) * e1 * e2 ^ 5 +
    ((-56 : K) / 6328125) * e1 * e2 ^ 4 * e3 + ((97 : K) / 6328125) * e1 * e2 ^ 4 +
    ((-133 : K) / 6328125) * e1 * e2 ^ 3 * e3 ^ 2 + ((-362 : K) / 6328125) * e1 * e2 ^ 3 * e3 +
    ((-92 : K) / 6328125) * e1 * e2 ^ 3 + ((-17 : K) / 421875) * e1 * e2 ^ 2 * e3 ^ 3 +
    ((-2 : K) / 140625) * e1 * e2 ^ 2 * e3 ^ 2 + ((434 : K) / 6328125) * e1 * e2 ^ 2 * e3 +
    ((9 : K) / 78125) * e1 * e2 * e3 ^ 3 + ((9 : K) / 78125) * e1 * e2 * e3 ^ 2 +
    ((-118 : K) / 1265625) * e1 * e3 ^ 4 + ((253 : K) / 6328125) * e1 * e3 ^ 3 +
    ((7 : K) / 253125) * e1 * e3 ^ 2 + ((1 : K) / 1406250) * e2 ^ 7 +
    ((1 : K) / 703125) * e2 ^ 6 + ((1 : K) / 703125) * e2 ^ 5 * e3 +
    ((4 : K) / 703125) * e2 ^ 5 + ((2 : K) / 253125) * e2 ^ 4 * e3 ^ 2 +
    ((14 : K) / 2109375) * e2 ^ 4 * e3 + ((88 : K) / 6328125) * e2 ^ 4 +
    ((-149 : K) / 6328125) * e2 ^ 3 * e3 ^ 2 + ((-436 : K) / 6328125) * e2 ^ 3 * e3 +
    ((14 : K) / 1265625) * e2 ^ 2 * e3 ^ 3 + ((299 : K) / 6328125) * e2 ^ 2 * e3 ^ 2 +
    ((4 : K) / 140625) * e2 ^ 2 * e3 + ((7 : K) / 253125) * e2 * e3 ^ 4 +
    ((253 : K) / 6328125) * e2 * e3 ^ 3 + ((-118 : K) / 1265625) * e2 * e3 ^ 2 +
    ((-7 : K) / 46875) * e3 ^ 4 + ((-7 : K) / 46875) * e3 ^ 3 := by
  simp only [y3c1, y3c1_0, y3c1_1, y3c1_2, y3c1_3, y3c1_4, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 4000000 in
theorem y3c2_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    y3c2 (Ne e1 e2 e3) =
    ((-1 : K) / 4218750) * e1 ^ 7 + ((1 : K) / 2109375) * e1 ^ 6 * e2 +
    ((-1 : K) / 2109375) * e1 ^ 6 * e3 + ((-1 : K) / 4218750) * e1 ^ 6 +
    ((-1 : K) / 4218750) * e1 ^ 5 * e2 ^ 2 + ((13 : K) / 2109375) * e1 ^ 5 * e2 * e3 +
    ((7 : K) / 2531250) * e1 ^ 5 * e2 + ((-29 : K) / 2109375) * e1 ^ 5 * e3 ^ 2 +
    ((-2 : K) / 2109375) * e1 ^ 5 * e3 + ((-8 : K) / 6328125) * e1 ^ 4 * e2 ^ 3 +
    ((7 : K) / 2109375) * e1 ^ 4 * e2 ^ 2 * e3 + ((-11 : K) / 2531250) * e1 ^ 4 * e2 ^ 2 +
    ((16 : K) / 2109375) * e1 ^ 4 * e2 * e3 ^ 2 + ((-31 : K) / 6328125) * e1 ^ 4 * e2 * e3 +
    ((4 : K) / 2109375) * e1 ^ 4 * e2 + ((4 : K) / 6328125) * e1 ^ 4 * e3 ^ 3 +
    ((3 : K) / 156250) * e1 ^ 4 * e3 ^ 2 + ((-41 : K) / 12656250) * e1 ^ 4 * e3 +
    ((-1 : K) / 4218750) * e1 ^ 3 * e2 ^ 4 + ((-7 : K) / 2109375) * e1 ^ 3 * e2 ^ 3 * e3 +
    ((17 : K) / 4218750) * e1 ^ 3 * e2 ^ 3 + ((-1 : K) / 234375) * e1 ^ 3 * e2 ^ 2 * e3 ^ 2 +
    ((-287 : K) / 6328125) * e1 ^ 3 * e2 ^ 2 * e3 + ((-131 : K) / 12656250) * e1 ^ 3 * e2 ^ 2 +
    ((376 : K) / 6328125) * e1 ^ 3 * e2 * e3 ^ 2 + ((151 : K) / 6328125) * e1 ^ 3 * e2 * e3 +
    ((-154 : K) / 6328125) * e1 ^ 3 * e3 ^ 3 + ((-11 : K) / 6328125) * e1 ^ 3 * e3 ^ 2 +
    ((-1 : K) / 421875) * e1 ^ 3 * e3 + ((1 : K) / 2109375) * e1 ^ 2 * e2 ^ 5 +
    ((4 : K) / 2109375) * e1 ^ 2 * e2 ^ 4 * e3 + ((2 : K) / 253125) * e1 ^ 2 * e2 ^ 4 +
    ((-19 : K) / 4218750) * e1 ^ 2 * e2 ^ 3 * e3 + ((59 : K) / 6328125) * e1 ^ 2 * e2 ^ 3 +
    ((8 : K) / 2109375) * e1 ^ 2 * e2 ^ 2 * e3 ^ 2 +
    ((49 : K) / 2531250) * e1 ^ 2 * e2 ^ 2 * e3 + ((-1 : K) / 234375) * e1 ^ 2 * e2 ^ 2 +
    ((26 : K) / 1265625) * e1 ^ 2 * e2 * e3 ^ 3 + ((-2 : K) / 421875) * e1 ^ 2 * e2 * e3 ^ 2 +
    ((49 : K) / 4218750) * e1 ^ 2 * e2 * e3 + ((-91 : K) / 6328125) * e1 ^ 2 * e3 ^ 3 +
    ((-167 : K) / 6328125) * e1 ^ 2 * e3 ^ 2 + ((-1 : K) / 4218750) * e1 * e2 ^ 6 +
    ((-1 : K) / 1265625) * e1 * e2 ^ 5 + ((-16 : K) / 6328125) * e1 * e2 ^ 4 * e3 +
    ((-47 : K) / 4218750) * e1 * e2 ^ 4 + ((-13 : K) / 2531250) * e1 * e2 ^ 3 * e3 ^ 2 +
    ((376 : K) / 6328125) * e1 * e2 ^ 3 * e3 + ((92 : K) / 6328125) * e1 * e2 ^ 3 +
    ((-499 : K) / 4218750) * e1 * e2 ^ 2 * e3 ^ 2 + ((-76 : K) / 1265625) * e1 * e2 ^ 2 * e3 +
    ((-13 : K) / 1265625) * e1 * e2 * e3 ^ 3 + ((-737 : K) / 12656250) * e1 * e2 * e3 ^ 2 +
    ((2 : K) / 140625) * e1 * e2 * e3 + ((-1 : K) / 50625) * e1 * e3 ^ 4 +
    ((121 : K) / 6328125) * e1 * e3 ^ 3 + ((61 : K) / 2531250) * e1 * e3 ^ 2 +
    ((1 : K) / 6328125) * e2 ^ 6 + ((1 : K) / 2531250) * e2 ^ 5 * e3 +
    ((-58 : K) / 6328125) * e2 ^ 5 + ((97 : K) / 6328125) * e2 ^ 4 * e3 +
    ((-22 : K) / 6328125) * e2 ^ 4 + ((7 : K) / 421875) * e2 ^ 3 * e3 ^ 2 +
    ((196 : K) / 6328125) * e2 ^ 3 * e3 + ((4 : K) / 6328125) * e2 ^ 3 +
    ((-1 : K) / 168750) * e2 ^ 2 * e3 ^ 3 + ((-43 : K) / 703125) * e2 ^ 2 * e3 ^ 2 +
    ((-22 : K) / 703125) * e2 ^ 2 * e3 + ((109 : K) / 843750) * e2 * e3 ^ 3 +
    ((209 : K) / 2109375) * e2 * e3 ^ 2 + ((1 : K) / 33750) * e3 ^ 4 +
    ((11 : K) / 4218750) * e3 ^ 3 + ((-2 : K) / 84375) * e3 ^ 2 := by
  simp only [y3c2, y3c2_0, y3c2_1, y3c2_2, y3c2_3, y3c2_4, Ne, Matrix.cons_val]
  ring

set_option maxHeartbeats 40000000 in
theorem det_yv_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    (Matrix.of (yv (Ne e1 e2 e3))).det =
      ((1 : K) / 384433593750) * T1 e1 e2 e3 * T2 e1 e2 e3 * T3 e1 e2 e3 * T4 e1 e2 e3 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, yv, Matrix.cons_val, y1c0_Ne, y1c1_Ne, y1c2_Ne, y2c0_Ne, y2c1_Ne,
    y2c2_Ne, y3c0_Ne, y3c1_Ne, y3c2_Ne, T1, T2, T3, T4]
  ring

/-! ## The fifteen synthemes -/

/-- Syntheme class 1: `D = (-1 : K) * l + m * n`, involution with centre `p = 0`, `k = l`. -/
def D1 {K : Type*} [Field K] (l m n : K) : K := (-1 : K) * l + m * n

def P1 {K : Type*} [Field K] (l m n : K) : K := 0

def K1 {K : Type*} [Field K] (l m n : K) : K := l

theorem cls1_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K1 l m n)
    (hD : D1 l m n = 0) :
    actC (Nr l m n) (s - P1 l m n) (P1 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K1, D1, P1] at *
  linear_combination ((-2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * s ^ 2 + (4 : K) * l * s + (-2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((2 : K) * l ^ 2 + (-4 : K) * l * s + (2 : K) * l) * hD

theorem cls1_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K1 l m n)
    (hD : D1 l m n = 0) :
    actC (Nr l m n) (s - P1 l m n) (P1 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K1, D1, P1] at *
  linear_combination ((4 : K) * l ^ 2 + (-4 : K) * l * m * n + (4 : K) * l * s ^ 2 + (4 : K) * l + (-4 : K) * m * n + (4 : K) * m * s ^ 2 + (4 : K) * n * s ^ 2 + (4 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 2 + (-4 : K) * l) * hD

theorem cls1_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K1 l m n)
    (hD : D1 l m n = 0) :
    actC (Nr l m n) (s - P1 l m n) (P1 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K1, D1, P1] at *
  linear_combination ((-2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * s ^ 2 + (-4 : K) * l * s + (-2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (-4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((2 : K) * l ^ 2 + (4 : K) * l * s + (2 : K) * l) * hD

/-- Syntheme class 2: `D = l + m * n + (-1 : K) * m + (-1 : K) * n`, involution with centre `p = (1 : K)`, `k = (-1 : K) * l + (1 : K)`. -/
def D2 {K : Type*} [Field K] (l m n : K) : K := l + m * n + (-1 : K) * m + (-1 : K) * n

def P2 {K : Type*} [Field K] (l m n : K) : K := (1 : K)

def K2 {K : Type*} [Field K] (l m n : K) : K := (-1 : K) * l + (1 : K)

theorem cls2_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K2 l m n)
    (hD : D2 l m n = 0) :
    actC (Nr l m n) (s - P2 l m n) (P2 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K2, D2, P2] at *
  linear_combination ((2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (-2 : K) * l * s ^ 2 + (-4 : K) * l * s + (-4 : K) * l + (-4 : K) * m * n + (-2 : K) * m * s ^ 2 + (4 : K) * m + (-2 : K) * n * s ^ 2 + (4 : K) * n + (4 : K) * s ^ 3 + (8 : K) * s ^ 2 + (4 : K) * s) * hs + ((-2 : K) * l ^ 2 + (4 : K) * l * s + (6 : K) * l + (-4 : K) * s + (-4 : K)) * hD

theorem cls2_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K2 l m n)
    (hD : D2 l m n = 0) :
    actC (Nr l m n) (s - P2 l m n) (P2 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K2, D2, P2] at *
  linear_combination ((-4 : K) * l ^ 2 + (-4 : K) * l * m * n + (4 : K) * l * m + (4 : K) * l * n + (4 : K) * l * s ^ 2 + (8 : K) * l + (8 : K) * m * n + (4 : K) * m * s ^ 2 + (-8 : K) * m + (4 : K) * n * s ^ 2 + (-8 : K) * n + (-16 : K) * s ^ 2) * hs + ((4 : K) * l ^ 2 + (-12 : K) * l + (8 : K)) * hD

theorem cls2_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K2 l m n)
    (hD : D2 l m n = 0) :
    actC (Nr l m n) (s - P2 l m n) (P2 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K2, D2, P2] at *
  linear_combination ((2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (-2 : K) * l * s ^ 2 + (4 : K) * l * s + (-4 : K) * l + (-4 : K) * m * n + (-2 : K) * m * s ^ 2 + (4 : K) * m + (-2 : K) * n * s ^ 2 + (4 : K) * n + (-4 : K) * s ^ 3 + (8 : K) * s ^ 2 + (-4 : K) * s) * hs + ((-2 : K) * l ^ 2 + (-4 : K) * l * s + (6 : K) * l + (4 : K) * s + (-4 : K)) * hD

/-- Syntheme class 3: `D = (-1 : K) * l * m + (-1 : K) * l * n + l + m * n`, involution with centre `p = l`, `k = l ^ 2 + (-1 : K) * l`. -/
def D3 {K : Type*} [Field K] (l m n : K) : K := (-1 : K) * l * m + (-1 : K) * l * n + l + m * n

def P3 {K : Type*} [Field K] (l m n : K) : K := l

def K3 {K : Type*} [Field K] (l m n : K) : K := l ^ 2 + (-1 : K) * l

theorem cls3_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K3 l m n)
    (hD : D3 l m n = 0) :
    actC (Nr l m n) (s - P3 l m n) (P3 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K3, D3, P3] at *
  linear_combination ((4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (4 : K) * l ^ 2 * s + (-4 : K) * l ^ 2 + (-4 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (8 : K) * l * s ^ 2 + (-4 : K) * l * s + (2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (-4 : K) * l ^ 2 * s + (6 : K) * l ^ 2 + (4 : K) * l * s + (-2 : K) * l) * hD

theorem cls3_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K3 l m n)
    (hD : D3 l m n = 0) :
    actC (Nr l m n) (s - P3 l m n) (P3 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K3, D3, P3] at *
  linear_combination ((-8 : K) * l ^ 2 * m + (-8 : K) * l ^ 2 * n + (8 : K) * l ^ 2 + (8 : K) * l * m * n + (4 : K) * l * m + (4 : K) * l * n + (-16 : K) * l * s ^ 2 + (-4 : K) * l + (-4 : K) * m * n + (4 : K) * m * s ^ 2 + (4 : K) * n * s ^ 2 + (4 : K) * s ^ 2) * hs + ((8 : K) * l ^ 3 + (-12 : K) * l ^ 2 + (4 : K) * l) * hD

theorem cls3_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K3 l m n)
    (hD : D3 l m n = 0) :
    actC (Nr l m n) (s - P3 l m n) (P3 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K3, D3, P3] at *
  linear_combination ((4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (-4 : K) * l ^ 2 * s + (-4 : K) * l ^ 2 + (-4 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (8 : K) * l * s ^ 2 + (4 : K) * l * s + (2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (-4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (4 : K) * l ^ 2 * s + (6 : K) * l ^ 2 + (-4 : K) * l * s + (-2 : K) * l) * hD

/-- Syntheme class 4: `D = l * m + (-1 : K) * l * n + (-1 : K) * l + n`, involution with centre `p = l`, `k = l ^ 2 + (-1 : K) * l * m`. -/
def D4 {K : Type*} [Field K] (l m n : K) : K := l * m + (-1 : K) * l * n + (-1 : K) * l + n

def P4 {K : Type*} [Field K] (l m n : K) : K := l

def K4 {K : Type*} [Field K] (l m n : K) : K := l ^ 2 + (-1 : K) * l * m

theorem cls4_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K4 l m n)
    (hD : D4 l m n = 0) :
    actC (Nr l m n) (s - P4 l m n) (P4 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K4, D4, P4] at *
  linear_combination ((-4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (4 : K) * l ^ 2 * s + (4 : K) * l ^ 2 + (2 : K) * l * m ^ 2 + (-2 : K) * l * m * n + (-4 : K) * l * m * s + (-2 : K) * l * m + (-4 : K) * l * n + (8 : K) * l * s ^ 2 + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (6 : K) * l ^ 2 * m + (-4 : K) * l ^ 2 * s + (-2 : K) * l * m ^ 2 + (4 : K) * l * m * s) * hD

theorem cls4_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K4 l m n)
    (hD : D4 l m n = 0) :
    actC (Nr l m n) (s - P4 l m n) (P4 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K4, D4, P4] at *
  linear_combination ((8 : K) * l ^ 2 * m + (-8 : K) * l ^ 2 * n + (-8 : K) * l ^ 2 + (-4 : K) * l * m ^ 2 + (4 : K) * l * m * n + (4 : K) * l * m + (8 : K) * l * n + (-16 : K) * l * s ^ 2 + (-4 : K) * m * n + (4 : K) * m * s ^ 2 + (4 : K) * n * s ^ 2 + (4 : K) * s ^ 2) * hs + ((8 : K) * l ^ 3 + (-12 : K) * l ^ 2 * m + (4 : K) * l * m ^ 2) * hD

theorem cls4_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K4 l m n)
    (hD : D4 l m n = 0) :
    actC (Nr l m n) (s - P4 l m n) (P4 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Ne, Matrix.cons_val, K4, D4, P4] at *
  linear_combination ((-4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (-4 : K) * l ^ 2 * s + (4 : K) * l ^ 2 + (2 : K) * l * m ^ 2 + (-2 : K) * l * m * n + (4 : K) * l * m * s + (-2 : K) * l * m + (-4 : K) * l * n + (8 : K) * l * s ^ 2 + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (-4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (6 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * s + (-2 : K) * l * m ^ 2 + (-4 : K) * l * m * s) * hD

theorem T1_Nr {K : Type*} [Field K] (l m n : K) :
    T1 (l + m + n) (l * m + l * n + m * n) (l * m * n) = D1 l m n * D1 m l n * D1 n l m := by
  simp only [T1, D1]; ring

theorem T2_Nr {K : Type*} [Field K] (l m n : K) :
    T2 (l + m + n) (l * m + l * n + m * n) (l * m * n) = D2 l m n * D2 m l n * D2 n l m := by
  simp only [T2, D2]; ring

theorem T3_Nr {K : Type*} [Field K] (l m n : K) :
    T3 (l + m + n) (l * m + l * n + m * n) (l * m * n) = D3 l m n * D3 m l n * D3 n l m := by
  simp only [T3, D3]; ring

theorem T4_Nr {K : Type*} [Field K] (l m n : K) :
    T4 (l + m + n) (l * m + l * n + m * n) (l * m * n) =
      D4 l m n * D4 l n m * D4 m l n * D4 m n l * D4 n l m * D4 n m l := by
  simp only [T4, D4]; ring

/-- **Clebsch's determinant on the root normal form is the product over the 15 synthemes.** -/
theorem det_yv_Nr {K : Type*} [Field K] [CharZero K] (l m n : K) :
    (Matrix.of (yv (Nr l m n))).det = ((1 : K) / 384433593750) *
      (D1 l m n * D1 m l n * D1 n l m) * (D2 l m n * D2 m l n * D2 n l m) *
      (D3 l m n * D3 m l n * D3 n l m) *
      (D4 l m n * D4 l n m * D4 m l n * D4 m n l * D4 n l m * D4 n m l) := by
  rw [Nr, det_yv_Ne, T1_Nr, T2_Nr, T3_Nr, T4_Nr]

/-! ## `J₁₀` -/

set_option maxHeartbeats 4000000 in
theorem J10_Ne {K : Type*} [Field K] (e1 e2 e3 : K) :
    J10 (Ne e1 e2 e3) =
    (-1024 : K) * e1 ^ 5 * e3 ^ 3 + (256 : K) * e1 ^ 4 * e2 ^ 2 * e3 ^ 2 +
    (2048 : K) * e1 ^ 4 * e2 * e3 ^ 3 + (-2048 : K) * e1 ^ 4 * e3 ^ 4 +
    (2048 : K) * e1 ^ 4 * e3 ^ 3 + (-512 : K) * e1 ^ 3 * e2 ^ 3 * e3 ^ 2 +
    (-512 : K) * e1 ^ 3 * e2 ^ 2 * e3 ^ 3 + (-512 : K) * e1 ^ 3 * e2 ^ 2 * e3 ^ 2 +
    (2048 : K) * e1 ^ 3 * e2 * e3 ^ 4 + (2560 : K) * e1 ^ 3 * e2 * e3 ^ 3 +
    (-1024 : K) * e1 ^ 3 * e3 ^ 5 + (2048 : K) * e1 ^ 3 * e3 ^ 4 +
    (-1024 : K) * e1 ^ 3 * e3 ^ 3 + (256 : K) * e1 ^ 2 * e2 ^ 4 * e3 ^ 2 +
    (-512 : K) * e1 ^ 2 * e2 ^ 3 * e3 ^ 3 + (-512 : K) * e1 ^ 2 * e2 ^ 3 * e3 ^ 2 +
    (256 : K) * e1 ^ 2 * e2 ^ 2 * e3 ^ 4 + (-9728 : K) * e1 ^ 2 * e2 ^ 2 * e3 ^ 3 +
    (256 : K) * e1 ^ 2 * e2 ^ 2 * e3 ^ 2 + (9216 : K) * e1 ^ 2 * e2 * e3 ^ 4 +
    (-9216 : K) * e1 ^ 2 * e2 * e3 ^ 3 + (-6912 : K) * e1 ^ 2 * e3 ^ 4 +
    (2048 : K) * e1 * e2 ^ 4 * e3 ^ 2 + (2560 : K) * e1 * e2 ^ 3 * e3 ^ 3 +
    (2048 : K) * e1 * e2 ^ 3 * e3 ^ 2 + (-9216 : K) * e1 * e2 ^ 2 * e3 ^ 4 +
    (9216 : K) * e1 * e2 ^ 2 * e3 ^ 3 + (4608 : K) * e1 * e2 * e3 ^ 5 +
    (4608 : K) * e1 * e2 * e3 ^ 4 + (4608 : K) * e1 * e2 * e3 ^ 3 + (-13824 : K) * e1 * e3 ^ 5 +
    (13824 : K) * e1 * e3 ^ 4 + (-1024 : K) * e2 ^ 5 * e3 ^ 2 + (2048 : K) * e2 ^ 4 * e3 ^ 3 +
    (-2048 : K) * e2 ^ 4 * e3 ^ 2 + (-1024 : K) * e2 ^ 3 * e3 ^ 4 +
    (2048 : K) * e2 ^ 3 * e3 ^ 3 + (-1024 : K) * e2 ^ 3 * e3 ^ 2 +
    (-6912 : K) * e2 ^ 2 * e3 ^ 4 + (13824 : K) * e2 * e3 ^ 5 + (-13824 : K) * e2 * e3 ^ 4 +
    (-6912 : K) * e3 ^ 6 + (13824 : K) * e3 ^ 5 + (-6912 : K) * e3 ^ 4 := by
  rw [J10_eq]
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9, Ne, Matrix.cons_val]
  ring

/-- `J₁₀` is `2⁸` times the discriminant. -/
theorem J10_Nr {K : Type*} [Field K] (l m n : K) :
    J10 (Nr l m n) = 256 * (l ^ 2 * m ^ 2 * n ^ 2 * (l - 1) ^ 2 * (m - 1) ^ 2 * (n - 1) ^ 2 *
      (l - m) ^ 2 * (l - n) ^ 2 * (m - n) ^ 2) := by
  rw [Nr, J10_Ne]; ring

theorem Nr_distinct {K : Type*} [Field K] {l m n : K} (h : J10 (Nr l m n) ≠ 0) :
    l ≠ 0 ∧ l ≠ 1 ∧ l ≠ m := by
  rw [J10_Nr] at h
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h <;> ring

set_option maxHeartbeats 4000000 in
/-- A double root at `∞` kills `J₁₀`. -/
theorem J10_zero_56 {K : Type*} [Field K] (a : Fin 7 → K) (h5 : a 5 = 0) (h6 : a 6 = 0) :
    J10 a = 0 := by
  rw [J10_eq]
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9, h5, h6]
  ring

set_option maxHeartbeats 4000000 in
/-- A double root at `0` kills `J₁₀`. -/
theorem J10_zero_01 {K : Type*} [Field K] (a : Fin 7 → K) (h0 : a 0 = 0) (h1 : a 1 = 0) :
    J10 a = 0 := by
  rw [J10_eq]
  simp only [J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8, J10R9, h0, h1]
  ring

/-! ## From an involution to the family `E a b` -/

/-- An even sextic with `J₁₀ ≠ 0` is equivalent to some `x⁶ + a x⁴ + b x² + 1`. -/
theorem even_to_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (g : Fin 7 → K)
    (h1 : g 1 = 0) (h3 : g 3 = 0) (h5 : g 5 = 0) (hJ : J10 g ≠ 0) : ∃ a b, Eqv g (E a b) := by
  have h6 : g 6 ≠ 0 := fun h => hJ (J10_zero_56 g h5 h)
  have h0 : g 0 ≠ 0 := fun h => hJ (J10_zero_01 g h h1)
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (g 0 / g 6) (by norm_num : 0 < 6)
  have hk' : g 6 * k ^ 6 = g 0 := by rw [hk]; field_simp
  have hk0 : k ≠ 0 := by rintro rfl; apply h0; rw [← hk']; ring
  refine ⟨g 4 * k ^ 4 / g 0, g 2 * k ^ 2 / g 0,
    (Eqv.of_actC g k 0 0 1 (1 / g 0) (by simpa using hk0) (by simpa using h0)).of_eq ?_⟩
  have key : actC g k 0 0 1 (1 / g 0) = ![g 0 / g 0, g 1 * k / g 0, g 2 * k ^ 2 / g 0,
      g 3 * k ^ 3 / g 0, g 4 * k ^ 4 / g 0, g 5 * k ^ 5 / g 0, g 6 * k ^ 6 / g 0] := by
    funext i; fin_cases i <;> simp [actC, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring
  rw [key, h1, h3, h5, hk', div_self h0]
  funext i; fin_cases i <;> simp [E]

/-- An involution `x ↦ p + k/(x - p)` (`k ≠ 0`) whose conjugate makes `f` even gives `f ≅ E a b`. -/
theorem inv_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (f : Fin 7 → K)
    (hJ : J10 f ≠ 0) (p k : K) (hk : k ≠ 0)
    (hodd : ∀ s : K, s ^ 2 = k → actC f (s - p) (p + s) (-1) 1 1 1 = 0 ∧
      actC f (s - p) (p + s) (-1) 1 1 3 = 0 ∧ actC f (s - p) (p + s) (-1) 1 1 5 = 0) :
    ∃ a b, Eqv f (E a b) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq k (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by rintro rfl; apply hk; rw [← hs]; ring
  have hE : Eqv f (actC f (s - p) (p + s) (-1) 1 1) := Eqv.of_actC _ _ _ _ _ _
    (by rw [show (s - p) * 1 - (p + s) * -1 = 2 * s by ring]; exact mul_ne_zero two_ne_zero hs0)
    one_ne_zero
  obtain ⟨o1, o3, o5⟩ := hodd s hs
  obtain ⟨a, b, hab⟩ := even_to_E _ o1 o3 o5 (hE.J10_ne_zero hJ)
  exact ⟨a, b, hE.trans hab⟩

theorem cls1_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D1 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨hl0, -, -⟩ := Nr_distinct hJ
  exact inv_E _ hJ (P1 l m n) (K1 l m n) (by simpa [K1] using hl0)
    fun s hs => ⟨cls1_odd1 l m n s hs hD, cls1_odd3 l m n s hs hD, cls1_odd5 l m n s hs hD⟩

theorem cls2_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D2 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨-, hl1, -⟩ := Nr_distinct hJ
  refine inv_E _ hJ (P2 l m n) (K2 l m n) ?_
    fun s hs => ⟨cls2_odd1 l m n s hs hD, cls2_odd3 l m n s hs hD, cls2_odd5 l m n s hs hD⟩
  rw [show K2 l m n = 1 - l by simp only [K2]; ring]
  exact sub_ne_zero.mpr (Ne.symm hl1)

theorem cls3_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D3 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨hl0, hl1, -⟩ := Nr_distinct hJ
  refine inv_E _ hJ (P3 l m n) (K3 l m n) ?_
    fun s hs => ⟨cls3_odd1 l m n s hs hD, cls3_odd3 l m n s hs hD, cls3_odd5 l m n s hs hD⟩
  rw [show K3 l m n = l * (l - 1) by simp only [K3]; ring]
  exact mul_ne_zero hl0 (sub_ne_zero.mpr hl1)

theorem cls4_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D4 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨hl0, -, hlm⟩ := Nr_distinct hJ
  refine inv_E _ hJ (P4 l m n) (K4 l m n) ?_
    fun s hs => ⟨cls4_odd1 l m n s hs hD, cls4_odd3 l m n s hs hD, cls4_odd5 l m n s hs hD⟩
  rw [show K4 l m n = l * (l - m) by simp only [K4]; ring]
  exact mul_ne_zero hl0 (sub_ne_zero.mpr hlm)

/-- Transport a class lemma along a permutation of the roots `l, m, n`. -/
theorem perm_E {K : Type*} [Field K] {l m n l' m' n' : K} (h1 : l' + m' + n' = l + m + n)
    (h2 : l' * m' + l' * n' + m' * n' = l * m + l * n + m * n) (h3 : l' * m' * n' = l * m * n)
    (hJ : J10 (Nr l m n) ≠ 0)
    (H : J10 (Nr l' m' n') ≠ 0 → ∃ a b, Eqv (Nr l' m' n') (E a b)) :
    ∃ a b, Eqv (Nr l m n) (E a b) := by
  rw [Nr_eq_of h1 h2 h3] at H; exact H hJ

/-- **Bolza's criterion on the normal form**: `det yv = 0` and `J₁₀ ≠ 0` give an extra
involution, hence an equivalence with some `x⁶ + a x⁴ + b x² + 1`. -/
theorem special_Nr {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hdet : (Matrix.of (yv (Nr l m n))).det = 0) (hJ : J10 (Nr l m n) ≠ 0) :
    ∃ a b, Eqv (Nr l m n) (E a b) := by
  rw [det_yv_Nr] at hdet
  rcases mul_eq_zero.mp hdet with h | h4
  · rcases mul_eq_zero.mp h with h | h3
    · rcases mul_eq_zero.mp h with h | h2
      · rcases mul_eq_zero.mp h with h | h1
        · norm_num at h
        · rcases mul_eq_zero.mp h1 with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact cls1_E l m n h hJ
            · exact perm_E (by ring) (by ring) (by ring) hJ (cls1_E m l n h)
          · exact perm_E (by ring) (by ring) (by ring) hJ (cls1_E n l m h)
      · rcases mul_eq_zero.mp h2 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact cls2_E l m n h hJ
          · exact perm_E (by ring) (by ring) (by ring) hJ (cls2_E m l n h)
        · exact perm_E (by ring) (by ring) (by ring) hJ (cls2_E n l m h)
    · rcases mul_eq_zero.mp h3 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact cls3_E l m n h hJ
        · exact perm_E (by ring) (by ring) (by ring) hJ (cls3_E m l n h)
      · exact perm_E (by ring) (by ring) (by ring) hJ (cls3_E n l m h)
  · rcases mul_eq_zero.mp h4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact cls4_E l m n h hJ
            · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E l n m h)
          · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E m l n h)
        · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E m n l h)
      · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E n l m h)
    · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E n m l h)

end T28Special
