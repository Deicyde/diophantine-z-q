import ZInQKernel.Model.Field.Euclidean

/-!
# Elements of norm zero

Blueprint: `compiler/natural/precision/norm-zero.md`.

`u² - 2v² = 0` over `ℚ` forces `u = v = 0`; equivalently an element of `K₀` of norm zero is
zero, and a nonzero `Y ∈ ℤ[s]` has nonzero integer norm `N(Y) = Y Ȳ`.
-/

namespace ZInQ.Compiler.Precision

/-- If `u² - 2v² = 0` with `u, v ∈ ℚ`, then `u = v = 0`. -/
theorem rat_eq_zero_of_sq_sub_two_sq {u v : ℚ} (h : u ^ 2 - 2 * v ^ 2 = 0) : u = 0 ∧ v = 0 := by
  have hz : QuadraticAlgebra.norm (⟨u, v⟩ : K0) = 0 := by rw [K0.norm_eq]; simpa using h
  have := K0.norm_eq_zero_iff.mp hz
  exact ⟨congrArg QuadraticAlgebra.re this, congrArg QuadraticAlgebra.im this⟩

/-- The integer form: `g² - 2h² ≠ 0` unless `g = h = 0`. -/
theorem intNorm_ne_zero {g h : ℤ} (hne : (g, h) ≠ (0, 0)) : g ^ 2 - 2 * h ^ 2 ≠ 0 := by
  intro e
  have e' : (g : ℚ) ^ 2 - 2 * (h : ℚ) ^ 2 = 0 := by exact_mod_cast e
  obtain ⟨h1, h2⟩ := rat_eq_zero_of_sq_sub_two_sq e'
  exact hne (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))

/-- An element of `K₀` of norm zero is zero. -/
theorem K0.eq_zero_of_norm_eq_zero {z : K0} (h : QuadraticAlgebra.norm z = 0) : z = 0 :=
  K0.norm_eq_zero_iff.mp h

/-- `Y Ȳ` is the integer `N(Y)`. -/
theorem Zs.mul_star_eq_norm (z : Zs) : z * star z = ((QuadraticAlgebra.norm z : ℤ) : Zs) := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, algebraMap_int_eq, eq_intCast]


/-- The integer test `N(Y) ≠ 0` decides `Y ≠ 0`. -/
theorem Zs.norm_ne_zero_iff {z : Zs} : QuadraticAlgebra.norm z ≠ 0 ↔ z ≠ 0 :=
  ⟨fun h hz => h (by simp [hz]), Zs.norm_ne_zero⟩

end ZInQ.Compiler.Precision
