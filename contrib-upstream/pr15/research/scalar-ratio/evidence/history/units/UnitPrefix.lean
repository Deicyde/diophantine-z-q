import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Integral-unit criterion, with zero cases retained

Received as an uncompiled candidate. Current verification is recorded in
`research/scalar-ratio/VERIFICATION.md`.

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

@[simp] lemma unitValue_one (R : Subring K) : unitValue R 1 = 1 := by
  simp [unitValue]

@[simp] lemma unitValue_mul (R : Subring K) (u w : Rˣ) :
    unitValue R (u * w) = unitValue R u * unitValue R w := by
  simp [unitValue]

@[simp] lemma unitValue_neg (R : Subring K) (u : Rˣ) :
    unitValue R (-u) = -unitValue R u := by
  simp [unitValue]

lemma unitValue_inv_mul (R : Subring K) (u : Rˣ) :
    unitValue R u⁻¹ * unitValue R u = 1 := by
  rw [← unitValue_mul]
  simp

lemma unitValue_ne_zero (R : Subring K) (u : Rˣ) : unitValue R u ≠ 0 := by
  intro hz
  have h := unitValue_inv_mul R u
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- Equality up to an INTEGRAL unit; meaningful also when both inputs are zero. -/
def UnitRelated (R : Subring K) (a b : K) : Prop :=
  ∃ u : Rˣ, a = unitValue R u * b

lemma unitRelated_scale_iff (R : Subring K) (c a b : K) (hc : c ≠ 0) :
    UnitRelated R (c * a) (c * b) ↔ UnitRelated R a b := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply mul_left_cancel₀ hc
    calc
      c * a = unitValue R u * (c * b) := hu
      _ = c * (unitValue R u * b) := by ring
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu]
    ring

lemma unitRelated_neg_left_iff (R : Subring K) (a b : K) :
    UnitRelated R (-a) b ↔ UnitRelated R a b := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    rw [unitValue_neg]
    calc
      a = -(-a) := (neg_neg a).symm
      _ = -(unitValue R u * b) := by rw [hu]
      _ = -unitValue R u * b := by ring
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    rw [unitValue_neg, hu]
    ring

lemma unitRelated_unit_left_iff (R : Subring K) (d : Rˣ) (a b : K) :
    UnitRelated R (unitValue R d * a) b ↔ UnitRelated R a b := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨d⁻¹ * u, ?_⟩
    rw [unitValue_mul]
    calc
      a = unitValue R d⁻¹ * (unitValue R d * a) := by
        rw [← mul_assoc, unitValue_inv_mul, one_mul]
      _ = unitValue R d⁻¹ * (unitValue R u * b) := by rw [hu]
      _ = _ := by ring
  · rintro ⟨u, hu⟩
    refine ⟨d * u, ?_⟩
    rw [unitValue_mul, hu]
    ring

lemma unitRelated_iff_quotient (R : Subring K) (a b : K) (hb : b ≠ 0) :
    UnitRelated R a b ↔ ∃ u : Rˣ, a / b = unitValue R u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (div_eq_iff hb).mpr hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (div_eq_iff hb).mp hu⟩

/-- These are the expressions proved to be coordinates in CommonStrict.lean,
not an alternative definition of `HasCoordinate`. -/
def finiteFormula (eta theta qF : K) : K := -eta * qF / theta

def singularFormula (delta eta theta qS : K) : K := delta * eta * qS / theta

/-- The division-free identity retains zero functional/evaluation cases. -/
theorem scalar_cross_identity (delta eta theta qF qS : K) :
    qS * (delta * finiteFormula eta theta qF) +
      qF * singularFormula delta eta theta qS = 0 := by
  unfold finiteFormula singularFormula
  ring

/-- Exact discrepancy after the determinant-line transport. Only the
singular cross scalar must be nonzero to form this quotient. -/
theorem transported_ratio (delta eta theta qF qS : K)
    (hd : delta ≠ 0) (he : eta ≠ 0) (ht : theta ≠ 0) (hs : qS ≠ 0) :
    delta * finiteFormula eta theta qF / singularFormula delta eta theta qS =
      -qF / qS := by
  unfold finiteFormula singularFormula
  field_simp [hd, he, ht, hs]

/-- Equal normalization gives exact transported tensors, even if both
functionals vanish. No cancellation of qF or qS is used. -/
theorem transported_eq_of_equal_cross (delta eta theta qF qS : K)
    (hq : qF = qS) :
    delta * finiteFormula eta theta qF = -singularFormula delta eta theta qS := by
  rw [hq]
  unfold finiteFormula singularFormula
  ring

/-- A common NONUNIT scale cancels. This theorem also handles qF=qS=0. -/
theorem transported_unit_criterion
    (R : Subring K) (delta eta theta qF qS : K)
    (hd : delta ≠ 0) (he : eta ≠ 0) (ht : theta ≠ 0) :
    UnitRelated R (delta * finiteFormula eta theta qF)
        (singularFormula delta eta theta qS) ↔ UnitRelated R qF qS := by
  let c := delta * eta / theta
  have hc : c ≠ 0 := div_ne_zero (mul_ne_zero hd he) ht
  have hf : delta * finiteFormula eta theta qF = c * (-qF) := by
    dsimp [finiteFormula, c]
    ring
  have hs : singularFormula delta eta theta qS = c * qS := by
    dsimp [singularFormula, c]
    ring
  rw [hf, hs, unitRelated_scale_iff R c (-qF) qS hc,
    unitRelated_neg_left_iff]

/-- Equality of the untransported coordinates up to an R-unit additionally
uses that det(J) is the image of an actual R-unit. -/
theorem integral_unit_criterion
    (R : Subring K) (d : Rˣ) (eta theta qF qS : K)
    (he : eta ≠ 0) (ht : theta ≠ 0) :
    UnitRelated R (finiteFormula eta theta qF)
      (singularFormula (unitValue R d) eta theta qS) ↔ UnitRelated R qF qS := by
  have h := transported_unit_criterion R (unitValue R d) eta theta qF qS
    (unitValue_ne_zero R d) he ht
  rw [unitRelated_unit_left_iff] at h
  exact h

/-- Any multiplicative valuation trivial on the integral units consumes
UnitRelated. No additive infinity or subtraction convention is hidden here. -/
theorem valuation_equal_of_unitRelated
    {G : Type*} [MonoidWithZero G] (R : Subring K) (nu : K →*₀ G)
    (hunits : ∀ u : Rˣ, nu (unitValue R u) = 1)
    {a b : K} (h : UnitRelated R a b) : nu a = nu b := by
  obtain ⟨u, hu⟩ := h
  rw [hu, map_mul, hunits, one_mul]


end Research.DerivativeSwitch.ScalarRatio
