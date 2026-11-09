import ZInQKernel.Model.Field.Basic
import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# The generator curve `E` and the point `P₀`

Blueprint: `model/field/generator-curve.md`, `model/field/generator-point-equation.md`,
`model/field/generator-point.md`.

`E = genCurve : y² = x³ - d² x` over `K₀`, `d = 75 - 53 s` (defined in
`ZInQKernel/Hypotheses/MordellWeil.lean`). It is the short Weierstrass curve `shortCurve (-d²)`
by definition. The group `E(K₀)` is Mathlib's `genCurve.toAffine.Point`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

theorem genCurve_eq_shortCurve : genCurve = shortCurve (-genD ^ 2) := rfl

/-- `d² = 11243 - 7950 s`. -/
theorem genD_sq : genD ^ 2 = ⟨11243, -7950⟩ := by
  ext <;> simp [genD, pow_two] <;> norm_num

/-- `A = -d² = -11243 + 7950 s`. -/
theorem neg_genD_sq : -genD ^ 2 = ⟨-11243, 7950⟩ := by
  rw [genD_sq]; ext <;> simp

/-- `N(d) = 75² - 2·53² = 7`. -/
theorem norm_genD : QuadraticAlgebra.norm genD = 7 := by
  rw [K0.norm_eq]; simp [genD]; norm_num

theorem genD_ne_zero : genD ≠ 0 := by
  intro h; have := congrArg QuadraticAlgebra.re h; simp [genD] at this

theorem genCurve_a₄ : genCurve.a₄ = -genD ^ 2 := rfl

theorem genCurve_equation_iff (x y : K0) :
    genCurve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - genD ^ 2 * x := by
  rw [genCurve_eq_shortCurve, shortCurve_equation_iff]; ring_nf

/-- The discriminant of `E` is `-64 A³ = 64 d⁶`. -/
theorem genCurve_Δ : genCurve.Δ = 64 * genD ^ 6 := by
  rw [genCurve_eq_shortCurve, shortCurve_Δ]; ring

theorem genCurve_Δ_ne_zero : genCurve.Δ ≠ 0 := by
  rw [genCurve_Δ]; exact mul_ne_zero (by norm_num) (pow_ne_zero _ genD_ne_zero)

instance shortCurve_neg_genD_sq_isElliptic : (shortCurve (-genD ^ 2)).IsElliptic :=
  shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero 2 genD_ne_zero))

/-- `E` is an elliptic curve. -/
instance genCurve_isElliptic : genCurve.IsElliptic :=
  shortCurve_neg_genD_sq_isElliptic

/-! ### Two-torsion of `E` -/

theorem genCurve_equation_zero : genCurve.toAffine.Equation 0 0 := by
  rw [genCurve_equation_iff]; ring

theorem genCurve_equation_genD : genCurve.toAffine.Equation genD 0 := by
  rw [genCurve_equation_iff]; ring

theorem genCurve_equation_neg_genD : genCurve.toAffine.Equation (-genD) 0 := by
  rw [genCurve_equation_iff]; ring

/-- The two-torsion point `(0, 0)` of `E`. -/
def genT0 : genCurve.toAffine.Point := Point.mk genCurve_equation_zero
/-- The two-torsion point `(d, 0)` of `E`. -/
def genTd : genCurve.toAffine.Point := Point.mk genCurve_equation_genD
/-- The two-torsion point `(-d, 0)` of `E`. -/
def genTnegd : genCurve.toAffine.Point := Point.mk genCurve_equation_neg_genD

/-- `E(K₀)[2] = {O, (0,0), (d,0), (-d,0)}`. -/
theorem genCurve_two_torsion (P : genCurve.toAffine.Point) :
    2 • P = 0 ↔ P = 0 ∨ P = genT0 ∨ P = genTd ∨ P = genTnegd := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [← Point.zero_def]
  · refine (shortCurve_two_nsmul_some_eq_zero_iff (A := -genD ^ 2) h).trans ?_
    simp only [genT0, genTd, genTnegd, Point.mk, reduceCtorEq, false_or]
    have he := (shortCurve_equation_iff _ x y).mp h.1
    constructor
    · rintro rfl
      have : x * (x - genD) * (x + genD) = 0 := by linear_combination -he
      rcases mul_eq_zero.mp this with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · left; simp only [Point.some.injEq]; exact ⟨h2, trivial⟩
        · right; left; simp only [Point.some.injEq]; exact ⟨sub_eq_zero.mp h2, trivial⟩
      · right; right; simp only [Point.some.injEq]; exact ⟨eq_neg_of_add_eq_zero_left h1, trivial⟩
    · rintro (h1 | h1 | h1) <;> simp only [Point.some.injEq] at h1 <;> exact h1.2

/-! ### The point `P₀` -/

/-- `x₀ = (1641 - 1160 s)/8 = 1641/8 - 145 s`. -/
def genX0 : K0 := ⟨1641 / 8, -145⟩

/-- `y₀ = (-123720 + 87483 s)/32 = -15465/4 + (87483/32) s`. -/
def genY0 : K0 := ⟨-15465 / 4, 87483 / 32⟩

theorem genX0_eq : genX0 = (1641 - 1160 * sqrt2) / 8 := by
  rw [eq_div_iff (by norm_num)]; ext <;> norm_num [genX0, sqrt2]

theorem genY0_eq : genY0 = (-123720 + 87483 * sqrt2) / 32 := by
  rw [eq_div_iff (by norm_num)]; ext <;> norm_num [genY0, sqrt2]

/-- `y₀² = x₀³ - d² x₀`: the coordinates of `P₀` satisfy the equation of `E`. -/
theorem genP0_curve : genY0 ^ 2 = genX0 ^ 3 - genD ^ 2 * genX0 := by
  rw [genD_sq]
  ext <;> simp [genX0, genY0, pow_succ] <;> norm_num

theorem genY0_ne_zero : genY0 ≠ 0 := by
  intro h; have := congrArg QuadraticAlgebra.re h; simp [genY0] at this

theorem genP0_equation : genCurve.toAffine.Equation genX0 genY0 :=
  (genCurve_equation_iff _ _).mpr genP0_curve

/-- The point `P₀ = ((1641 - 1160 s)/8, (-123720 + 87483 s)/32)` of `E(K₀)`. -/
def genP0 : genCurve.toAffine.Point := Point.mk genP0_equation

theorem genP0_ne_zero : genP0 ≠ 0 := Point.some_ne_zero _

end ZInQ
