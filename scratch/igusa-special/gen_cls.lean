/-- Syntheme class 1: `D = (-1 : K) * l + m * n`, involution with centre `p = 0`, `k = l`. -/
def D1 {K : Type*} [Field K] (l m n : K) : K := (-1 : K) * l + m * n

def P1 {K : Type*} [Field K] (l m n : K) : K := 0

def K1 {K : Type*} [Field K] (l m n : K) : K := l

theorem cls1_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K1 l m n)
    (hD : D1 l m n = 0) :
    actC (Nr l m n) (s - P1 l m n) (P1 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K1, D1, P1] at *
  linear_combination ((-2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * s ^ 2 + (4 : K) * l * s + (-2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((2 : K) * l ^ 2 + (-4 : K) * l * s + (2 : K) * l) * hD

theorem cls1_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K1 l m n)
    (hD : D1 l m n = 0) :
    actC (Nr l m n) (s - P1 l m n) (P1 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K1, D1, P1] at *
  linear_combination ((4 : K) * l ^ 2 + (-4 : K) * l * m * n + (4 : K) * l * s ^ 2 + (4 : K) * l + (-4 : K) * m * n + (4 : K) * m * s ^ 2 + (4 : K) * n * s ^ 2 + (4 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 2 + (-4 : K) * l) * hD

theorem cls1_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K1 l m n)
    (hD : D1 l m n = 0) :
    actC (Nr l m n) (s - P1 l m n) (P1 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K1, D1, P1] at *
  linear_combination ((-2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * s ^ 2 + (-4 : K) * l * s + (-2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (-4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((2 : K) * l ^ 2 + (4 : K) * l * s + (2 : K) * l) * hD

/-- Syntheme class 2: `D = l + m * n + (-1 : K) * m + (-1 : K) * n`, involution with centre `p = (1 : K)`, `k = (-1 : K) * l + (1 : K)`. -/
def D2 {K : Type*} [Field K] (l m n : K) : K := l + m * n + (-1 : K) * m + (-1 : K) * n

def P2 {K : Type*} [Field K] (l m n : K) : K := (1 : K)

def K2 {K : Type*} [Field K] (l m n : K) : K := (-1 : K) * l + (1 : K)

theorem cls2_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K2 l m n)
    (hD : D2 l m n = 0) :
    actC (Nr l m n) (s - P2 l m n) (P2 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K2, D2, P2] at *
  linear_combination ((2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (-2 : K) * l * s ^ 2 + (-4 : K) * l * s + (-4 : K) * l + (-4 : K) * m * n + (-2 : K) * m * s ^ 2 + (4 : K) * m + (-2 : K) * n * s ^ 2 + (4 : K) * n + (4 : K) * s ^ 3 + (8 : K) * s ^ 2 + (4 : K) * s) * hs + ((-2 : K) * l ^ 2 + (4 : K) * l * s + (6 : K) * l + (-4 : K) * s + (-4 : K)) * hD

theorem cls2_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K2 l m n)
    (hD : D2 l m n = 0) :
    actC (Nr l m n) (s - P2 l m n) (P2 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K2, D2, P2] at *
  linear_combination ((-4 : K) * l ^ 2 + (-4 : K) * l * m * n + (4 : K) * l * m + (4 : K) * l * n + (4 : K) * l * s ^ 2 + (8 : K) * l + (8 : K) * m * n + (4 : K) * m * s ^ 2 + (-8 : K) * m + (4 : K) * n * s ^ 2 + (-8 : K) * n + (-16 : K) * s ^ 2) * hs + ((4 : K) * l ^ 2 + (-12 : K) * l + (8 : K)) * hD

theorem cls2_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K2 l m n)
    (hD : D2 l m n = 0) :
    actC (Nr l m n) (s - P2 l m n) (P2 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K2, D2, P2] at *
  linear_combination ((2 : K) * l ^ 2 + (2 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (-2 : K) * l * s ^ 2 + (4 : K) * l * s + (-4 : K) * l + (-4 : K) * m * n + (-2 : K) * m * s ^ 2 + (4 : K) * m + (-2 : K) * n * s ^ 2 + (4 : K) * n + (-4 : K) * s ^ 3 + (8 : K) * s ^ 2 + (-4 : K) * s) * hs + ((-2 : K) * l ^ 2 + (-4 : K) * l * s + (6 : K) * l + (4 : K) * s + (-4 : K)) * hD

/-- Syntheme class 3: `D = (-1 : K) * l * m + (-1 : K) * l * n + l + m * n`, involution with centre `p = l`, `k = l ^ 2 + (-1 : K) * l`. -/
def D3 {K : Type*} [Field K] (l m n : K) : K := (-1 : K) * l * m + (-1 : K) * l * n + l + m * n

def P3 {K : Type*} [Field K] (l m n : K) : K := l

def K3 {K : Type*} [Field K] (l m n : K) : K := l ^ 2 + (-1 : K) * l

theorem cls3_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K3 l m n)
    (hD : D3 l m n = 0) :
    actC (Nr l m n) (s - P3 l m n) (P3 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K3, D3, P3] at *
  linear_combination ((4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (4 : K) * l ^ 2 * s + (-4 : K) * l ^ 2 + (-4 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (8 : K) * l * s ^ 2 + (-4 : K) * l * s + (2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (-4 : K) * l ^ 2 * s + (6 : K) * l ^ 2 + (4 : K) * l * s + (-2 : K) * l) * hD

theorem cls3_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K3 l m n)
    (hD : D3 l m n = 0) :
    actC (Nr l m n) (s - P3 l m n) (P3 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K3, D3, P3] at *
  linear_combination ((-8 : K) * l ^ 2 * m + (-8 : K) * l ^ 2 * n + (8 : K) * l ^ 2 + (8 : K) * l * m * n + (4 : K) * l * m + (4 : K) * l * n + (-16 : K) * l * s ^ 2 + (-4 : K) * l + (-4 : K) * m * n + (4 : K) * m * s ^ 2 + (4 : K) * n * s ^ 2 + (4 : K) * s ^ 2) * hs + ((8 : K) * l ^ 3 + (-12 : K) * l ^ 2 + (4 : K) * l) * hD

theorem cls3_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K3 l m n)
    (hD : D3 l m n = 0) :
    actC (Nr l m n) (s - P3 l m n) (P3 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K3, D3, P3] at *
  linear_combination ((4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (-4 : K) * l ^ 2 * s + (-4 : K) * l ^ 2 + (-4 : K) * l * m * n + (-2 : K) * l * m + (-2 : K) * l * n + (8 : K) * l * s ^ 2 + (4 : K) * l * s + (2 : K) * l + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (-4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (4 : K) * l ^ 2 * s + (6 : K) * l ^ 2 + (-4 : K) * l * s + (-2 : K) * l) * hD

/-- Syntheme class 4: `D = l * m + (-1 : K) * l * n + (-1 : K) * l + n`, involution with centre `p = l`, `k = l ^ 2 + (-1 : K) * l * m`. -/
def D4 {K : Type*} [Field K] (l m n : K) : K := l * m + (-1 : K) * l * n + (-1 : K) * l + n

def P4 {K : Type*} [Field K] (l m n : K) : K := l

def K4 {K : Type*} [Field K] (l m n : K) : K := l ^ 2 + (-1 : K) * l * m

theorem cls4_odd1 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K4 l m n)
    (hD : D4 l m n = 0) :
    actC (Nr l m n) (s - P4 l m n) (P4 l m n + s) (-1) 1 1 1 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K4, D4, P4] at *
  linear_combination ((-4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (4 : K) * l ^ 2 * s + (4 : K) * l ^ 2 + (2 : K) * l * m ^ 2 + (-2 : K) * l * m * n + (-4 : K) * l * m * s + (-2 : K) * l * m + (-4 : K) * l * n + (8 : K) * l * s ^ 2 + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (6 : K) * l ^ 2 * m + (-4 : K) * l ^ 2 * s + (-2 : K) * l * m ^ 2 + (4 : K) * l * m * s) * hD

theorem cls4_odd3 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K4 l m n)
    (hD : D4 l m n = 0) :
    actC (Nr l m n) (s - P4 l m n) (P4 l m n + s) (-1) 1 1 3 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K4, D4, P4] at *
  linear_combination ((8 : K) * l ^ 2 * m + (-8 : K) * l ^ 2 * n + (-8 : K) * l ^ 2 + (-4 : K) * l * m ^ 2 + (4 : K) * l * m * n + (4 : K) * l * m + (8 : K) * l * n + (-16 : K) * l * s ^ 2 + (-4 : K) * m * n + (4 : K) * m * s ^ 2 + (4 : K) * n * s ^ 2 + (4 : K) * s ^ 2) * hs + ((8 : K) * l ^ 3 + (-12 : K) * l ^ 2 * m + (4 : K) * l * m ^ 2) * hD

theorem cls4_odd5 {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K4 l m n)
    (hD : D4 l m n = 0) :
    actC (Nr l m n) (s - P4 l m n) (P4 l m n + s) (-1) 1 1 5 = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K4, D4, P4] at *
  linear_combination ((-4 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * n + (-4 : K) * l ^ 2 * s + (4 : K) * l ^ 2 + (2 : K) * l * m ^ 2 + (-2 : K) * l * m * n + (4 : K) * l * m * s + (-2 : K) * l * m + (-4 : K) * l * n + (8 : K) * l * s ^ 2 + (2 : K) * m * n + (-2 : K) * m * s ^ 2 + (-2 : K) * n * s ^ 2 + (-4 : K) * s ^ 3 + (-2 : K) * s ^ 2) * hs + ((-4 : K) * l ^ 3 + (6 : K) * l ^ 2 * m + (4 : K) * l ^ 2 * s + (-2 : K) * l * m ^ 2 + (-4 : K) * l * m * s) * hD
