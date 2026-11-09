import ZInQKernel.Assembly.Local.SixLocalTests
import ZInQKernel.Compiler.Precision

/-!
# The six local tests in the form of the value-test template

Blueprint: `assembly/value-templates/six-local-tests.md`.

The relation `Test n κ t` is defined in `ZInQKernel/Assembly/Local/SixLocalTests.lean` (task
assembly-local), with the local parameter `Mult.zCoord`, the inverse abscissa `Mult.wCoord` and
rational casts into `K₀`. The value-test template computes the same tests with `zPt` (the local
parameter of the precision chapter), `wPt` below and `algebraMap ℚ K₀`. This file records these
forms (`vtD`, `vtR0`, `vtA0`, `vtR`, `vtW`, `vtTheta`) and proves that they give the same relation
(`test_iff`).
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine Compiler.Precision

/-- The inverse abscissa `w(P) = 1/x` of an affine point of `E(K₀)`; `w(O) = 0`. -/
noncomputable def wPt : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x _ _ => 1 / x

@[simp] theorem wPt_zero : wPt 0 = 0 := rfl

@[simp] theorem wPt_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    wPt (.some x y h) = 1 / x := rfl

theorem wCoord_eq_wPt (P : genCurve.toAffine.Point) : Mult.wCoord (A := -genD ^ 2) P = wPt P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem zCoord_eq_zPt (P : genCurve.toAffine.Point) : Mult.zCoord (A := -genD ^ 2) P = zPt P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

/-- The six tests `D₁, …, D₆` with `zPt`, `wPt` and `algebraMap`. -/
noncomputable def vtD (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) : Fin 6 → K0 :=
  ![wPt (h • genP0), wPt (s₀ • genP0), star (wPt ((h - κ) • genP0)),
    star (wPt ((s₀ - κ * n) • genP0)),
    zPt (s₀ • genP0) / zPt (h • genP0) - algebraMap ℚ K0 t,
    star (zPt ((s₀ - κ * n) • genP0) / zPt ((h - κ) • genP0)) - algebraMap ℚ K0 t]

/-- `R₀ = η · 2730⁶ · F(t)`. -/
def vtR0 (t η : ℚ) : ℚ := η * 2730 ^ 6 * Mult.contactPoly t

/-- `a₀ = 1 - R₀ q²`. -/
def vtA0 (t η q : ℚ) : ℚ := 1 - vtR0 t η * q ^ 2

/-- `R = R₀ a₀²`. -/
def vtR (t η q : ℚ) : ℚ := vtR0 t η * vtA0 t η q ^ 2

/-- `W = ∏ⱼ (1 + R Cⱼ²)` with `Cⱼ = Dⱼ / F(t)`. -/
noncomputable def vtW (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) (η q : ℚ) : K0 :=
  ∏ j : Fin 6, (1 + algebraMap ℚ K0 (vtR t η q) *
    (vtD n κ t h s₀ j / algebraMap ℚ K0 (Mult.contactPoly t)) ^ 2)

/-- `Θ = Tr(W⁻¹)`. -/
noncomputable def vtTheta (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) (η q : ℚ) : ℚ :=
  QuadraticAlgebra.trace (vtW n κ t h s₀ η q)⁻¹

theorem algebraMap_K0 (r : ℚ) : algebraMap ℚ K0 r = (r : K0) := eq_ratCast _ r

theorem testD_eq_vtD (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) : testD n κ t h s₀ = vtD n κ t h s₀ := by
  funext j
  fin_cases j
  · exact wCoord_eq_wPt _
  · exact wCoord_eq_wPt _
  · exact congrArg star (wCoord_eq_wPt _)
  · exact congrArg star (wCoord_eq_wPt _)
  · show _ = _ / _ - _
    rw [algebraMap_K0]
    exact congrArg (· - (t : K0)) (congrArg₂ (· / ·) (zCoord_eq_zPt _) (zCoord_eq_zPt _))
  · show _ = star (_ / _) - _
    rw [algebraMap_K0]
    exact congrArg (· - (t : K0)) (congrArg star
      (congrArg₂ (· / ·) (zCoord_eq_zPt _) (zCoord_eq_zPt _)))

theorem testR_eq_vtR (η q t : ℚ) : testR η q t = vtR t η q := rfl

theorem poleW_eq_vtW (n κ : ℤ) (t : ℚ) (h s₀ : ℤ) (η q : ℚ) :
    poleW (testR η q t) (testC n κ t h s₀) = vtW n κ t h s₀ η q := by
  simp only [poleW, testC, vtW, testD_eq_vtD, algebraMap_K0, testR_eq_vtR]

/-- **The six local tests in the form of the value-test template.** -/
theorem test_iff (n κ : ℤ) (t : ℚ) :
    Test n κ t ↔ κ ≠ 0 ∧ t ∉ contactSet ∧ ∃ (h s₀ : ℤ) (η q : ℚ), h ≠ 0 ∧ h ≠ κ ∧ η ^ 2 = 1 ∧
      vtA0 t η q ≠ 0 ∧ vtW n κ t h s₀ η q ≠ 0 ∧ vtTheta n κ t h s₀ η q ≠ 0 ∧
      PoleSoluble (vtR t η q / vtTheta n κ t h s₀ η q ^ 2) := by
  simp only [Test, poleTheta, poleW_eq_vtW]
  rfl

/-- `2730⁶ = 413976684737889000000`. -/
theorem pow_six_2730_rat : (2730 : ℚ) ^ 6 = 413976684737889000000 := by norm_num

end ZInQ.Assembly
