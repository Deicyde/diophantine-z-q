import Challenge.CommonStrict

/-!
# Integral-unit criterion, with zero cases retained

Frozen concrete specification: selected theorem proof holes are intentional.
No solution module is imported. Reviewed against the intended mathematical contract.

IMPORTANT: `IsUnit` in the fraction FIELD would be vacuous for nonzero
scalars. `UnitRelated R a b` instead exhibits a unit of the specified
INTEGRAL subring `R`. The common scale need not be an R-unit.
-/

namespace Research.DerivativeSwitch.ScalarRatio

open Matrix
open scoped Matrix

variable {K : Type*} [Field K]

/-- Image of an integral unit in the generic coefficient field. -/
def unitValue (R : Subring K) (u : Rˣ) : K := R.subtype (u : R)

def UnitRelated (R : Subring K) (a b : K) : Prop :=
  ∃ u : Rˣ, a = unitValue R u * b

def finiteFormula (eta theta qF : K) : K := -eta * qF / theta

def singularFormula (delta eta theta qS : K) : K := delta * eta * qS / theta

/-- The division-free identity retains zero functional/evaluation cases. -/
theorem transported_ratio (delta eta theta qF qS : K)
    (hd : delta ≠ 0) (he : eta ≠ 0) (ht : theta ≠ 0) (hs : qS ≠ 0) :
    delta * finiteFormula eta theta qF / singularFormula delta eta theta qS =
      -qF / qS := by sorry

theorem transported_unit_criterion
    (R : Subring K) (delta eta theta qF qS : K)
    (hd : delta ≠ 0) (he : eta ≠ 0) (ht : theta ≠ 0) :
    UnitRelated R (delta * finiteFormula eta theta qF)
        (singularFormula delta eta theta qS) ↔ UnitRelated R qF qS := by sorry

theorem integral_unit_criterion
    (R : Subring K) (d : Rˣ) (eta theta qF qS : K)
    (he : eta ≠ 0) (ht : theta ≠ 0) :
    UnitRelated R (finiteFormula eta theta qF)
      (singularFormula (unitValue R d) eta theta qS) ↔ UnitRelated R qF qS := by sorry

theorem valuation_equal_of_unitRelated
    {G : Type*} [MonoidWithZero G] (R : Subring K) (nu : K →*₀ G)
    (hunits : ∀ u : Rˣ, nu (unitValue R u) = 1)
    {a b : K} (h : UnitRelated R a b) : nu a = nu b := by sorry

namespace CommonStrictData

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- User-facing theorem on coordinates supplied independently by their
cofactor specifications, not by assigning them the output formulas. -/
theorem actual_coordinate_ratio (d : CommonStrictData K I) (uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix _ _ K) *ᵥ d.v)) d.lamS uS)
    (hqS : d.qS ≠ 0) : d.delta * uF / uS = -d.qF / d.qS := by sorry

theorem actual_integral_unit_criterion
    (d : CommonStrictData K I) (R : Subring K) (detJ : Rˣ)
    (hJ : d.delta = unitValue R detJ) (uF uS : K)
    (huF : HasCoordinate (join d.D0 d.AF) (cycle d.hF d.v) d.lamF uF)
    (huS : HasCoordinate (join d.D0 d.AS)
      (cycle d.hS ((d.J : Matrix _ _ K) *ᵥ d.v)) d.lamS uS) :
    UnitRelated R uF uS ↔ UnitRelated R d.qF d.qS := by sorry

end CommonStrictData

end Research.DerivativeSwitch.ScalarRatio
