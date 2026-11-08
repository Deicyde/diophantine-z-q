# Implementation note: The discriminant of Q(√d)

- Owner: pp-quadfield (plan step 3.2). Namespace `ZInQ.Progressions`; modules import Mathlib (and earlier `Progressions` modules) only.
- Lean name: proposed `ZInQ.Progressions.abs_discr_quadField_le`.
- Draft:
  ```lean
  theorem abs_discr_quadField_le {d : ℤ} [Fact (¬ IsSquare (d : ℚ))] :
      |NumberField.discr (QuadField d)| ≤ 4 * |d|
  ```
- Mathlib: `NumberField.discr`, `NumberField.discr_eq_discr` (discriminant of an integral basis), `Algebra.discr_of_matrix_vecMul` (`discr (b ᵥ* A) = det A ^ 2 * discr b`), `Algebra.discr_def` and `Algebra.trace` of `1, √d` (`QuadraticAlgebra.trace` lemmas), integrality of `√d` (`IsIntegral` of a root of `X^2 - d`).
- Only the upper bound is needed (the residue bound). The exact value (`d` or `4d`) is optional.
