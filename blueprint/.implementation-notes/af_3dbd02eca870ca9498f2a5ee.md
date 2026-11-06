# Implementation note: Jacobian formulas on the weighted model

- Lean names: `ZInQ.Compiler.Precision.jdbl`, `jadd` (explicit formulas over a commutative
  ring), `jdbl_equation`, `jadd_equation`, `jdbl_affine`, `jadd_affine`, `jac_P0`.
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
  theorem jac_P0 : (P0J 1)^2 = (P0J 0)^3 + Acoef*(P0J 0)*(P0J 2)^4   -- in ℤ[√2] or K0
  ```
- Checked while writing: items 1-6 hold at 30 random points on random curves modulo the
  prime 1000003, and item 9 (the curve equation for $(X_0,Y_0,Z_0)$) holds exactly.
- Mathlib: `WeierstrassCurve.Jacobian` API, `linear_combination`, `ring`.
- Upstream reuse: none.
- FINITE COMPUTATION: item 9 is a closed identity in `ℤ[√2]` (`decide`/`norm_num` on
  integer pairs: `Y0^2 = X0^3 + A*X0*Z0^4` with 12-digit integers). Others are ring
  identities (not finite computations).
- Difficulty: medium (items 1-2 cofactors; transport to Mathlib points).
