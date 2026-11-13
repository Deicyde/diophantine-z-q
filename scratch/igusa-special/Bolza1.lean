import ZInQKernel.HDecomp.Textbook.Igusa.Generic

namespace T28Special
open PkgI1

/-- `x(x-1)(x³ - e₁x² + e₂x - e₃)` as a binary sextic (root at `∞`). -/
def Ne {K : Type*} [Field K] (e1 e2 e3 : K) : Fin 7 → K :=
  ![0, e3, -(e2 + e3), e1 + e2, -(1 + e1), 1, 0]

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
set_option maxHeartbeats 40000000 in
theorem det_yv_Ne {K : Type*} [Field K] (e1 e2 e3 : K) :
    (Matrix.of (yv (Ne e1 e2 e3))).det =
      ((1 : K) / 384433593750) * T1 e1 e2 e3 * T2 e1 e2 e3 * T3 e1 e2 e3 * T4 e1 e2 e3 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, yv, Ne, Matrix.cons_val, y1c0, y1c1, y1c2, y2c0, y2c1, y2c2, y3c0,
    y3c0_0, y3c0_1, y3c0_2, y3c0_3, y3c0_4, y3c1, y3c1_0, y3c1_1, y3c1_2, y3c1_3, y3c1_4, y3c2,
    y3c2_0, y3c2_1, y3c2_2, y3c2_3, y3c2_4, T1, T2, T3, T4]
  ring

end T28Special
