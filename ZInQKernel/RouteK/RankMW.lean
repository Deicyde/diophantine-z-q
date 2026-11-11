import ZInQKernel.RouteK.RankMW.Index
import ZInQKernel.RouteK.RankMW.Image
import ZInQKernel.RouteK.RankMW.Torsion

/-!
# Mordell–Weil for the congruent number curves

`C_d(ℚ)` is finitely generated for `C_d : y² = x³ - d² x`, `d ≠ 0` (`fg_points`).

The descent theorem `AddCommGroup.fg_of_descent'` (Mathlib, `GroupTheory/Descent.lean`) needs a
finite index `[C_d(ℚ) : 2C_d(ℚ)]`, a nonnegative height with the approximate parallelogram law and
the Northcott property; the naïve height of `Mathlib/NumberTheory/Height/EllipticCurve.lean` has
the last three over the number field `ℚ`. The finite index comes from the two-isogeny descent:
`φ : C_d → C'_d : y² = x³ + 4d² x` is a homomorphism (`RankMW/PhiAdd.lean`), the Kummer images of
`C_d(ℚ)` and `C'_d(ℚ)` lie in the classes of the signed divisors of `d²` and `4d²`
(`RankMW/Image.lean`), and `[E : 2E] ≤ #α(E) · #α'(E')` (`RankMW/Index.lean`).

`RankMW/Torsion.lean`: `C_d(ℚ)[2] = {O, (0,0), (d,0), (-d,0)}` (`twoTorsion_card`).
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent Height

/-- **`[C_d(ℚ) : 2C_d(ℚ)]` is finite.** -/
theorem finiteIndex_two_points (d : ℕ) (hd : d ≠ 0) :
    (nsmulAddMonoidHom (α := (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) 2).range.FiniteIndex := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have := mwIsElliptic d hd
  have : (shortCurve (-4 * -(d : ℚ) ^ 2)).IsElliptic :=
    shortCurve_isElliptic (by
      rw [show -4 * -(d : ℚ) ^ 2 = 4 * d ^ 2 by ring]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hd'))
  have : (shortCurve (-4 * (-4 * -(d : ℚ) ^ 2))).IsElliptic :=
    shortCurve_isElliptic (by
      rw [show -4 * (-4 * -(d : ℚ) ^ 2) = -16 * d ^ 2 by ring]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hd'))
  have h1 : (Set.range (kummer (-(d : ℚ) ^ 2))).Finite := by
    have h := mwKummer_range_finite (-(d : ℤ) ^ 2) (neg_ne_zero.mpr (pow_ne_zero 2 hdZ))
    rwa [show (((-(d : ℤ) ^ 2 : ℤ)) : ℚ) = -(d : ℚ) ^ 2 by push_cast; ring] at h
  have h2 : (Set.range (kummer (-4 * -(d : ℚ) ^ 2))).Finite := by
    have h := mwKummer_range_finite (4 * (d : ℤ) ^ 2) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hdZ))
    rwa [show (((4 * (d : ℤ) ^ 2 : ℤ)) : ℚ) = -4 * -(d : ℚ) ^ 2 by push_cast; ring] at h
  exact mwFiniteIndex_two_of_kummer (b := -(d : ℚ) ^ 2) (b'' := -4 * (-4 * -(d : ℚ) ^ 2)) rfl rfl
    h1 h2

/-- **Mordell–Weil for `C_d`**: `C_d(ℚ)` is finitely generated. -/
theorem fg_points (d : ℕ) (hd : d ≠ 0) :
    AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point := by
  have := mwIsElliptic d hd
  obtain ⟨C, hC⟩ := approx_parallelogram_law (shortCurve (-(d : ℚ) ^ 2)).toAffine
  exact AddCommGroup.fg_of_descent' (finiteIndex_two_points d hd)
    (fun P => by rw [Point.naiveHeight_eq_logHeight]; exact logHeight_nonneg _) hC

end ZInQ.RouteK.Rank
