# el-special log

Notation: `C_d : y² = x³ − d²x`; `T_a = {d ∈ ℚ*/ℚ*² : C_d has a point with x ∈ aℚ*²}`.
By cr3-map-literature R1, `T_a = {a(a²s⁴ − 1) : s ∈ ℙ¹(ℚ)}` (classes). Route K's `Φ` for
multiplier `m` needs `N` with `N ∈ T_β` and `Nθ ∈ T_β` (cr3-map-needs L5).

## S1. Slot freedom does not change existence (algebra; cf. cr3-map-literature R3)
`∃N: N ∈ T_β ∧ Nθ ∈ T_β` ⇔ `θ ∈ T_β·T_β` ⇔ `X_{β,θ}: w² = θ(β²s⁴−1)(β²t⁴−1)` has a rational
point. The auxiliary primes of `N` (slots `q₀, r_p, r_ℓ`, F6/F7) are a choice of fibre; they
cannot create points. Any prime-structured choice of `N` only matters as a proof device.

## C1. Prime APs and explicit points (`c1_triangle_classes.py`, <1 s) — VERIFIED
- Input: coprime `2 ≤ b < a < 40`, `N = b(a−b)a(a+b)` (AP `a−b, a, a+b`, difference `b`).
- Points `x = Na/b, −Nb/a, N(a+b)/(a−b), −N(a−b)/(a+b)` lie on `C_N`: 1892/1892.
- Their abscissa classes are exactly `{±(a²−b²), ±ab}` (all cases).
- 8076 prime 3-APs (`a < 2000`): the class `a²−b²` always has exactly 2 primes; `ab` has `a`
  plus `sqf(b)`. Primality plays no role in the points (they exist for all `a, b`); a prime AP
  only restricts which classes occur. To get class `β` one needs `a²−b² ≡ β` or `ab ≡ ±β`, which
  is the conic parametrization R1/R5 again. Green–Tao adds nothing to point production.
