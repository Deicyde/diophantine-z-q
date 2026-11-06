# Implementation note: Jacobian formulas on the weighted model

- Lean names: `ZInQ.Compiler.Precision.jdbl`, `jadd` (explicit formulas over a commutative
  ring), `jdbl_equation`, `jadd_equation`, `jdbl_affine`, `jadd_affine`.
- Recommended route: relate to Mathlib's Jacobian formulas for `genCurve` (with
  `a₁ = a₂ = a₃ = a₆ = 0`, `a₄ = A`): `WeierstrassCurve.Jacobian.dblXYZ`, `addXYZ`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`) and
  `Jacobian.Point.toAffineAddEquiv`, `Jacobian.toAffine_of_Z_ne_zero` (`.../Jacobian/Point.lean`).
  Mathlib's formulas differ from the chapter's by unit scalings; prove
  `jdbl P ≈ dblXYZ P` and `jadd P Q ≈ addXYZ P Q` (equivalence under `u • P`) with `ring`/
  `linear_combination` using the curve equations, then transport. Alternatively prove items
  1-6 directly by `linear_combination (cofactor) * hE`.
- Draft:
  ```lean
  def jdbl {R : Type*} [CommRing R] (A : R) (P : Fin 3 → R) : Fin 3 → R :=
    let M := 3*P 0^2 + A*P 2^4; let S := 4*P 0*P 1^2; let X3 := M^2 - 2*S
    ![X3, M*(S - X3) - 8*P 1^4, 2*P 1*P 2]
  theorem jdbl_equation {R} [CommRing R] (A : R) (P : Fin 3 → R)
      (h : P 1^2 = P 0^3 + A*P 0*P 2^4) :
      (jdbl A P) 1^2 = (jdbl A P) 0^3 + A*(jdbl A P) 0*(jdbl A P) 2^4
  ```
- Checked while writing: items 1-6 hold at 30 random points on random curves modulo the
  prime 1000003. The reviewer re-checked items 1 and 2 symbolically (sympy: the
  remainders of `E(dbl P)` modulo `E(P)` and of `E(add P1 P2)` modulo `E(P1)`, `E(P2)` in
  `Y`, `Y1`, `Y2` vanish), so cofactors over `ℤ` exist.
- Mathlib: `WeierstrassCurve.Jacobian` API, `linear_combination`, `ring`.
- Upstream reuse: none.
- FINITE COMPUTATION: no (the fixed point, former item 9, is the separate leaf
  `jac_P0`). Items 1-6 are ring identities.
- Difficulty: medium (items 1-2 cofactors; transport to Mathlib points).
