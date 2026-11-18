import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinCongruenceSeries
import FiniteUnitConvolution

/-!
# Actual primitive Eisenstein modular forms in same-level product spans

The actual gcd-one series is recovered through a finite inverse matrix
whose entries depend only on the level, weight and unit permutations.
The raw congruence forms have the required N^-k normalization. Nonprimitive
rows are proved zero from their empty gcd-one gamma sets. No spanning,
invertibility, tail-bound or coefficient-representation hypothesis is used.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinSeriesMembership

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinGcdData PrimitiveEisensteinNormalization PrimitiveEisensteinUnitSeries
open PrimitiveEisensteinCongruenceSeries TorsionWeightThree

/-- The actual finite inverse coefficients have no upper-half-plane parameter. -/
def primitiveInverseCoefficients (N : ℕ) [NeZero N] (k : ℕ) :
    Matrix (PrimitiveRow N) (PrimitiveRow N) ℂ :=
  FiniteUnitConvolution.unitConvolutionInverseCoefficients k (unitPermutation N) (fun d => d.Coprime N)

/-- Actual raw congruence values are the concrete finite convolution of actual primitive values. -/
theorem raw_values_eq_convolution (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (fun a : PrimitiveRow N => rawCongruenceForm N hN k hk a.1 τ) =
      (FiniteUnitConvolution.unitConvolutionMatrix k (unitPermutation N) (fun d => d.Coprime N)).mulVec
        (primitiveValues N k τ) := by
  rw [FiniteUnitConvolution.unitConvolutionMatrix, Matrix.add_mulVec, Matrix.one_mulVec,
    FiniteUnitConvolution.permutationTailMatrix_mulVec k hk]
  funext a
  rw [rawCongruenceForm_eq_primitive_add_tail N hN k hk a τ]
  simp only [Pi.add_apply]
  congr 1
  apply tsum_congr
  intro n
  unfold unitCoefficient FiniteUnitConvolution.complexInversePower
  by_cases hd : (n+2).Coprime N
  · simp only [ite_eq_left hd]
  · simp only [ite_eq_right hd, zero_mul]

/-- Every primitive series is an actual finite constant complex combination of genuine raw forms. -/
theorem actual_primitive_finite_combination (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : PrimitiveRow N) (τ : ℍ) :
    eisensteinSeries a.1 (k : ℤ) τ = ∑ b : PrimitiveRow N,
      primitiveInverseCoefficients N k a b * rawCongruenceForm N hN k hk b.1 τ := by
  exact FiniteUnitConvolution.unitConvolution_coefficients_independent_of_parameter k hk
    (unitPermutation N) (fun d => d.Coprime N)
    (fun τ : ℍ => fun b : PrimitiveRow N => rawCongruenceForm N hN k hk b.1 τ)
    (fun τ : ℍ => primitiveValues N k τ)
    (raw_values_eq_convolution N hN k hk) τ a

/-- A genuine modular-form finite combination with the proved actual inverse coefficients. -/
def primitiveCombinationForm (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : PrimitiveRow N) : Weight N (k : ℤ) :=
  ∑ b : PrimitiveRow N, primitiveInverseCoefficients N k a b • rawCongruenceForm N hN k hk b.1

theorem primitiveCombinationForm_apply_actual (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : PrimitiveRow N) (τ : ℍ) :
    primitiveCombinationForm N hN k hk a τ = eisensteinSeries a.1 (k : ℤ) τ := by
  simp only [primitiveCombinationForm, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  exact (actual_primitive_finite_combination N hN k hk a τ).symm

theorem primitiveCombinationForm_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : PrimitiveRow N) :
    primitiveCombinationForm N hN k hk a ∈ TorsionInvariantForms.homogeneousProductSpan N (by omega) k := by
  unfold primitiveCombinationForm
  apply Submodule.sum_mem
  intro b _
  exact Submodule.smul_mem _ _ (rawCongruenceForm_mem N hN k hk b.1)

/-- Equality of the actual Mathlib primitive modular form and the proved finite combination. -/
theorem eisensteinSeriesMF_eq_primitiveCombination (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : PrimitiveRow N) :
    ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a.1 =
      primitiveCombinationForm N hN k hk a := by
  apply DFunLike.ext
  intro τ
  change eisensteinSeries a.1 (k : ℤ) τ = primitiveCombinationForm N hN k hk a τ
  exact (primitiveCombinationForm_apply_actual N hN k hk a τ).symm

/-- The actual Mathlib gcd-one Eisenstein modular form is in the SAME-level Good product span. -/
theorem actual_primitive_eisensteinSeriesMF_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) :
    ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a ∈
      TorsionInvariantForms.homogeneousProductSpan N (by omega) k := by
  by_cases ha : IsCoprime (a 0) (a 1)
  · let row : PrimitiveRow N := ⟨a, ha⟩
    rw [show a = row.1 from rfl, eisensteinSeriesMF_eq_primitiveCombination N hN k hk row]
    exact primitiveCombinationForm_mem N hN k hk row
  · rw [eisensteinSeriesMF_eq_zero_nonprimitive (by exact_mod_cast hk : (3 : ℤ) ≤ k) a ha]
    exact Submodule.zero_mem _

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinSeriesMembership
