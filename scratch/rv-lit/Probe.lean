import ZInQKernel.Model.Field.ShortWeierstrass
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
open ZInQ
-- the curve of the CR3 Props is y^2 = x^3 - d^2 x
example (d : ℕ) : (shortCurve (-(d : ℚ) ^ 2)).a₄ = -((d : ℚ) ^ 2) := rfl
-- Mathlib's Γ has junk value 0 at 0 (so the unrestricted FunctionalEquation5 fails at s = 0)
example : Complex.Gamma 0 = 0 := Complex.Gamma_zero
-- analyticOrderAt junk: 0 at a non-analytic point
example (f : ℂ → ℂ) (z : ℂ) (h : ¬ AnalyticAt ℂ f z) : analyticOrderAt f z = 0 := by
  simp [analyticOrderAt, h]
