import Mathlib

/-! Timing test for the rational certificate of the main sum (C_3). -/

def uRe (a b : ℕ) : ℤ :=
  if (a % 4, b % 4) = (1, 0) ∨ (a % 4, b % 4) = (3, 2) then 1
  else if (a % 4, b % 4) = (3, 0) ∨ (a % 4, b % 4) = (1, 2) then -1 else 0
def uIm (a b : ℕ) : ℤ :=
  if (a % 4, b % 4) = (0, 3) ∨ (a % 4, b % 4) = (2, 1) then 1
  else if (a % 4, b % 4) = (0, 1) ∨ (a % 4, b % 4) = (2, 3) then -1 else 0
def jac12 (n : ℕ) : ℤ :=
  if n % 12 = 1 ∨ n % 12 = 11 then 1 else if n % 12 = 5 ∨ n % 12 = 7 then -1 else 0

def qterm (M : ℕ) (j1 j2 m n : ℕ) : ℚ :=
  let a1 : ℤ := j1 - M * m
  let a2 : ℤ := j2 - M * n
  let N : ℕ := (a1 ^ 2 + a2 ^ 2).toNat
  let J : ℤ := jac12 (j1 ^ 2 + j2 ^ 2)
  if N = 0 then 0 else ((J * uRe j1 j2 * a1 - J * uIm j1 j2 * a2 : ℤ) : ℚ) / (4 * N)

def lo (M : ℕ) (j1 j2 m n : ℕ) (l u : ℚ) : ℚ :=
  let a1 : ℤ := j1 - M * m
  let a2 : ℤ := j2 - M * n
  let N : ℕ := (a1 ^ 2 + a2 ^ 2).toNat
  let q := qterm M j1 j2 m n
  if 0 ≤ q then q * l ^ N else q * u ^ N

theorem test : (1.4 : ℚ) ≤ ∑ j1 ∈ Finset.range 12, ∑ j2 ∈ Finset.range 12, ∑ m ∈ Finset.range 2,
    ∑ n ∈ Finset.range 2, lo 12 j1 j2 m n (1223 / 1250) (1957 / 2000) := by
  decide +kernel
