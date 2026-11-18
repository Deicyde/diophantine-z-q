import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# The actual inverse-square finite permutation convolution

The exact d=2 term is one quarter. The remaining inverse-square terms are
bounded by a genuine telescoping series, so the whole tail is at most three
quarters. The finite sup-norm estimate has no cardinality loss. Thus the
literal guarded permutation matrix has a genuine ordinary inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

open Filter
open scoped BigOperators Topology Matrix

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoFiniteConvolution

/-- The actual scalar tail beginning at d=2. -/
def inverseSquareTail (n : ℕ) : ℝ := (((n + 2 : ℕ) : ℝ) ^ 2)⁻¹

/-- Half of a reciprocal telescoping difference. -/
def telescopingSeries (n : ℕ) : ℝ :=
  (2 * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))⁻¹

lemma telescopingSeries_nonneg (n : ℕ) : 0 ≤ telescopingSeries n := by
  unfold telescopingSeries
  positivity

lemma telescopingSeries_eq_sub (n : ℕ) :
    telescopingSeries n = (1 / 2 : ℝ) *
      (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹) := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [telescopingSeries, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp [h1, h2] <;> ring

lemma telescopingSeries_sum_range (M : ℕ) :
    (∑ n ∈ Finset.range M, telescopingSeries n) =
      (1 / 2 : ℝ) * (1 - ((M + 1 : ℕ) : ℝ)⁻¹) := by
  have h : (∑ n ∈ Finset.range M,
      (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹)) =
      1 - ((M + 1 : ℕ) : ℝ)⁻¹ := by
    simpa [Nat.add_assoc] using
      Finset.sum_range_sub' (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) M
  simp_rw [telescopingSeries_eq_sub]
  rw [← Finset.mul_sum, h]

lemma hasSum_telescopingSeries : HasSum telescopingSeries (1 / 2 : ℝ) := by
  have hlim : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  apply (hasSum_iff_tendsto_nat_of_nonneg telescopingSeries_nonneg (1 / 2 : ℝ)).2
  simpa only [telescopingSeries_sum_range, sub_zero, mul_one] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim).const_mul (1 / 2 : ℝ)

/-- The sharpened majorant keeps the exact first inverse square. -/
def squareMajorant (n : ℕ) : ℝ :=
  2 * telescopingSeries n - if n = 0 then 1 / 4 else 0

lemma hasSum_squareMajorant : HasSum squareMajorant (3 / 4 : ℝ) := by
  have h := (hasSum_telescopingSeries.mul_left 2).sub (hasSum_ite_eq (0 : ℕ) (1 / 4 : ℝ))
  unfold squareMajorant
  simpa only [show (2 : ℝ) * (1 / 2) - 1 / 4 = 3 / 4 by norm_num] using! h

lemma inverseSquareTail_nonneg (n : ℕ) : 0 ≤ inverseSquareTail n := by
  unfold inverseSquareTail
  positivity

lemma inverseSquareTail_le_majorant (n : ℕ) : inverseSquareTail n ≤ squareMajorant n := by
  by_cases hn : n = 0
  · subst n
    norm_num [inverseSquareTail, squareMajorant, telescopingSeries]
  · have hp : 0 < ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by positivity
    have hd : ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have he : 2 * telescopingSeries n =
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))⁻¹ := by
      simp only [telescopingSeries, mul_inv]
      ring
    simp only [squareMajorant, ite_eq_right hn, sub_zero, he, inverseSquareTail]
    exact inv_anti₀ hp hd

/-- Concrete weight-two summability, with no assumed convergence or high-weight theorem. -/
theorem summable_inverseSquareTail : Summable inverseSquareTail :=
  Summable.of_nonneg_of_le inverseSquareTail_nonneg inverseSquareTail_le_majorant
    hasSum_squareMajorant.summable

/-- The actual complete d≥2 inverse-square tail is at most three quarters. -/
theorem inverseSquareTail_sum_le : (∑' n : ℕ, inverseSquareTail n) ≤ (3 / 4 : ℝ) :=
  hasSum_le inverseSquareTail_le_majorant summable_inverseSquareTail.hasSum hasSum_squareMajorant

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Literal inverse-square entries of a guarded finite permutation tail. -/
def tailEntry (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (i j : I) (n : ℕ) : ℂ :=
  if guard (n + 2) ∧ j = σ (n + 2) i then (((n + 2 : ℕ) : ℂ) ^ 2)⁻¹ else 0

/-- The actual matrix, not a supplied linear operator with a desired norm bound. -/
def tailMatrix (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) : Matrix I I ℂ :=
  Matrix.of fun i j => ∑' n : ℕ, tailEntry σ guard i j n

/-- Identity plus the literal inverse-square permutation tail. -/
def convolutionMatrix (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) : Matrix I I ℂ :=
  1 + tailMatrix σ guard

lemma norm_complex_square (n : ℕ) : ‖(((n + 2 : ℕ) : ℂ) ^ 2)⁻¹‖ = inverseSquareTail n := by
  simp only [inverseSquareTail, norm_inv, Complex.norm_pow, Complex.norm_natCast]

lemma norm_tailEntry_le (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (i j : I) (n : ℕ) :
    ‖tailEntry σ guard i j n‖ ≤ inverseSquareTail n := by
  unfold tailEntry
  split_ifs
  · exact (norm_complex_square n).le
  · simpa only [norm_zero] using inverseSquareTail_nonneg n

lemma tailEntry_summable (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (i j : I) :
    Summable (tailEntry σ guard i j) :=
  summable_inverseSquareTail.of_norm_bounded (norm_tailEntry_le σ guard i j)

lemma norm_orbitTerm_le (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (x : I → ℂ) (i : I) (n : ℕ) :
    ‖(if guard (n + 2) then (((n + 2 : ℕ) : ℂ) ^ 2)⁻¹ * x (σ (n + 2) i) else 0 : ℂ)‖ ≤
      inverseSquareTail n * ‖x‖ := by
  by_cases hg : guard (n + 2)
  · simp only [ite_eq_left hg, norm_mul, norm_complex_square]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x (σ (n + 2) i))
      (inverseSquareTail_nonneg n)
  · simp only [ite_eq_right hg, norm_zero]
    exact mul_nonneg (inverseSquareTail_nonneg n) (norm_nonneg x)

lemma orbitTail_summable (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) (i : I) :
    Summable (fun n : ℕ => if guard (n + 2) then
      (((n + 2 : ℕ) : ℂ) ^ 2)⁻¹ * x (σ (n + 2) i) else 0) :=
  (summable_inverseSquareTail.mul_right ‖x‖).of_norm_bounded (norm_orbitTerm_le σ guard x i)

/-- The matrix action is the literal single-coordinate convolution; exchange is justified termwise. -/
theorem tailMatrix_mulVec (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    (tailMatrix σ guard).mulVec x =
      fun i => ∑' n : ℕ, if guard (n + 2) then
        (((n + 2 : ℕ) : ℂ) ^ 2)⁻¹ * x (σ (n + 2) i) else 0 := by
  funext i
  change (∑ j : I, (∑' n : ℕ, tailEntry σ guard i j n) * x j) = _
  calc
    _ = ∑' n : ℕ, ∑ j : I, tailEntry σ guard i j n * x j := by
      simpa only [tsum_mul_right] using
        (Summable.tsum_finsetSum (s := Finset.univ)
          (f := fun j n => tailEntry σ guard i j n * x j)
          (fun j _ => (tailEntry_summable σ guard i j).mul_right (x j))).symm
    _ = _ := by
      apply tsum_congr
      intro n
      by_cases hg : guard (n + 2)
      · simp [tailEntry, hg, ite_mul]
      · simp [tailEntry, hg]

/-- The concrete finite sup-norm contraction has no factor involving the number of indices. -/
theorem norm_tailMatrix_mulVec_le (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    ‖(tailMatrix σ guard).mulVec x‖ ≤ (3 / 4 : ℝ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) (norm_nonneg x))).2
  intro i
  rw [tailMatrix_mulVec σ guard x]
  change ‖∑' n : ℕ, if guard (n + 2) then
    (((n + 2 : ℕ) : ℂ) ^ 2)⁻¹ * x (σ (n + 2) i) else 0‖ ≤ _
  calc
    _ ≤ (∑' n : ℕ, inverseSquareTail n) * ‖x‖ :=
      tsum_of_norm_bounded (summable_inverseSquareTail.hasSum.mul_right ‖x‖)
        (norm_orbitTerm_le σ guard x i)
    _ ≤ (3 / 4 : ℝ) * ‖x‖ := mul_le_mul_of_nonneg_right inverseSquareTail_sum_le (norm_nonneg x)

/-- Concrete injectivity of the actual weight-two identity perturbation. -/
theorem convolutionMatrix_injective (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    Function.Injective (convolutionMatrix σ guard).mulVec := by
  intro x y hxy
  have hzero : (convolutionMatrix σ guard).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsum : (x - y) + (tailMatrix σ guard).mulVec (x - y) = 0 := by
    simpa only [convolutionMatrix, Matrix.add_mulVec, Matrix.one_mulVec] using hzero
  have hneg : (tailMatrix σ guard).mulVec (x - y) = -(x - y) := eq_neg_of_add_eq_zero_right hsum
  have hbound := norm_tailMatrix_mulVec_le σ guard (x - y)
  rw [hneg, norm_neg] at hbound
  apply eq_of_norm_sub_le_zero
  linarith only [hbound]

/-- Ordinary finite matrix invertibility is produced without an invertibility premise. -/
theorem convolutionMatrix_isUnit (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    IsUnit (convolutionMatrix σ guard) :=
  (Matrix.mulVec_injective_iff_isUnit (A := convolutionMatrix σ guard)).mp
    (convolutionMatrix_injective σ guard)

lemma convolutionMatrix_det_isUnit (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    IsUnit (convolutionMatrix σ guard).det :=
  (Matrix.isUnit_iff_isUnit_det (convolutionMatrix σ guard)).mp (convolutionMatrix_isUnit σ guard)

/-- The ordinary adjugate/determinant inverse is a true left inverse. -/
theorem convolutionMatrix_inv_mul (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    (convolutionMatrix σ guard)⁻¹ * convolutionMatrix σ guard = 1 :=
  Matrix.nonsing_inv_mul _ (convolutionMatrix_det_isUnit σ guard)

/-- The same ordinary inverse is a true right inverse. -/
theorem convolutionMatrix_mul_inv (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    convolutionMatrix σ guard * (convolutionMatrix σ guard)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (convolutionMatrix_det_isUnit σ guard)

/-- Recovery by the concrete usual matrix inverse. -/
theorem convolutionMatrix_recover (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    ((convolutionMatrix σ guard)⁻¹).mulVec ((convolutionMatrix σ guard).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, convolutionMatrix_inv_mul σ guard, Matrix.one_mulVec]

/-- Literal action of the matrix beginning with its genuine identity term. -/
theorem convolutionMatrix_mulVec (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    (convolutionMatrix σ guard).mulVec x =
      fun i => x i + ∑' n : ℕ, if guard (n + 2) then
        (((n + 2 : ℕ) : ℂ) ^ 2)⁻¹ * x (σ (n + 2) i) else 0 := by
  rw [convolutionMatrix, Matrix.add_mulVec, Matrix.one_mulVec, tailMatrix_mulVec σ guard x]
  rfl

#print axioms summable_inverseSquareTail
#print axioms inverseSquareTail_sum_le
#print axioms tailMatrix_mulVec
#print axioms norm_tailMatrix_mulVec_le
#print axioms convolutionMatrix_isUnit
#print axioms convolutionMatrix_recover

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoFiniteConvolution
