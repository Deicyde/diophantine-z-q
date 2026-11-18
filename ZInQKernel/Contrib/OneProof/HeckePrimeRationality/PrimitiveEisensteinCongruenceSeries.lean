import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinGrid
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightPrincipalEisensteinForms

/-!
# Actual unscaled congruence forms for primitive inversion

The raw form is the already verified grid form multiplied by N^-k. Its
actual value is the unrestricted congruence-vector series, and the proved
primitive unit convolution applies without a missing normalization factor.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinCongruenceSeries

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinGcdData PrimitiveEisensteinNormalization PrimitiveEisensteinUnitSeries
open PrimitiveEisensteinGrid TorsionWeightThree

/-- The actual unscaled raw form includes the required N^-k factor. -/
def rawCongruenceForm (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) : Weight N (k : ℤ) :=
  ((N : ℂ) ^ k)⁻¹ • AllWeightPrincipalEisensteinForms.principalEisensteinForm N hN k hk
    (residueLift a 0) (residueLift a 1)

/-- Literal equality with the actual unscaled unrestricted vector series. -/
theorem rawCongruenceForm_apply (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (τ : ℍ) :
    rawCongruenceForm N hN k hk a τ = unrestrictedSeries N a k τ := by
  change ((N : ℂ) ^ k)⁻¹ * AllWeightPrincipalEisensteinForms.principalEisensteinForm N hN k hk
    (residueLift a 0) (residueLift a 1) τ = _
  rw [AllWeightPrincipalEisensteinForms.principalEisensteinForm_apply_actual,
    unrestrictedSeries_eq_grid N (by omega)]
  have hc : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega : N ≠ 0))
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The actual raw form stays in the existing same-level Good homogeneous product span. -/
theorem rawCongruenceForm_mem (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    rawCongruenceForm N hN k hk a ∈ TorsionInvariantForms.homogeneousProductSpan N (by omega) k :=
  Submodule.smul_mem _ _ (AllWeightPrincipalEisensteinForms.principalEisensteinForm_mem N hN k hk
    (residueLift a 0) (residueLift a 1))

/-- The actual raw form satisfies the closed primitive-plus-unit-tail identity. -/
theorem rawCongruenceForm_eq_primitive_add_tail (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : PrimitiveRow N) (τ : ℍ) :
    rawCongruenceForm N hN k hk a.1 τ = primitiveValues N k τ a + ∑' n : ℕ,
      unitCoefficient N k (n+2) * primitiveValues N k τ (unitPermutation N (n+2) a) := by
  rw [rawCongruenceForm_apply]
  exact unrestrictedSeries_eq_primitive_add_tail N hN a k hk τ

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinCongruenceSeries
