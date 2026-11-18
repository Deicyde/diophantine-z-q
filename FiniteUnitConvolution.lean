import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite unit-convolution inversion

Actual inverse powers at natural exponents at least three are dominated by
an explicit nonnegative telescoping series with sum one half. This supplies
summability and a finite sup-norm contraction for guarded permutation tails.
The identity perturbation is a unit, and its usual matrix inverse supplies
constant coefficients independent of any external parameter.

All finite index types are allowed, including the empty type. The full
positive-index series is identified only with explicit identity data at one.
No assertion about a primitive series or a modular-form family is assumed.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace FiniteUnitConvolution

/-- The actual reciprocal of a natural power, with its natural argument cast to the reals. -/
def inversePower (k d : ℕ) : ℝ := ((d : ℝ) ^ k)⁻¹

/-- Actual inverse powers of natural arguments are nonnegative, including at zero. -/
theorem inversePower_nonneg (k d : ℕ) : 0 ≤ inversePower k d := by
  unfold inversePower
  exact inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg d) k)

/-- Pointwise comparison with the telescoping denominator on the genuine tail. -/
theorem inversePower_le_telescoping {k d : ℕ} (hk : 3 ≤ k) (hd : 2 ≤ d) :
    inversePower k d ≤ (2 * (d : ℝ) * ((d : ℝ) - 1))⁻¹ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd1 : 1 ≤ (d : ℝ) := by linarith
  have hdpos : 0 < (d : ℝ) := by linarith
  have hpred : 0 < (d : ℝ) - 1 := by linarith
  have hden : 0 < 2 * (d : ℝ) * ((d : ℝ) - 1) :=
    mul_pos (mul_pos (by norm_num) hdpos) hpred
  have hsq : 2 * ((d : ℝ) - 1) ≤ (d : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hcube : 2 * (d : ℝ) * ((d : ℝ) - 1) ≤ (d : ℝ) ^ 3 := by
    calc
      2 * (d : ℝ) * ((d : ℝ) - 1) = (d : ℝ) * (2 * ((d : ℝ) - 1)) := by
        ring
      _ ≤ (d : ℝ) * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq hd0
      _ = (d : ℝ) ^ 3 := by ring
  unfold inversePower
  exact inv_anti₀ hden (hcube.trans (pow_le_pow_right₀ hd1 hk))

/-- The explicit telescoping majorant, with both positive tail indices cast from naturals. -/
def telescopingTail (n : ℕ) : ℝ :=
  (2 * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))⁻¹

theorem telescopingTail_nonneg (n : ℕ) : 0 ≤ telescopingTail n := by
  unfold telescopingTail
  exact inv_nonneg.mpr
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (n + 2)))
      (Nat.cast_nonneg (n + 1)))

/-- The predecessor after shifting by two is exactly the cast of the next natural. -/
theorem inversePower_tail_le_telescoping {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    inversePower k (n + 2) ≤ telescopingTail n := by
  have hpred : ((n + 2 : ℕ) : ℝ) - 1 = ((n + 1 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring
  simpa only [telescopingTail, hpred] using
    (inversePower_le_telescoping hk (show 2 ≤ n + 2 by omega))

/-- Every term is half of the difference of two consecutive reciprocal tail indices. -/
theorem telescopingTail_eq_half_sub (n : ℕ) :
    telescopingTail n =
      (1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (n : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) + 2 ≠ 0 := by linarith
  simp only [telescopingTail, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp [h1, h2] <;> ring

/-- The finite telescoping identity holds for every cutoff, including the empty cutoff. -/
theorem sum_range_telescopingTail_factored (N : ℕ) :
    (∑ n ∈ Finset.range N, telescopingTail n) =
      (1 / 2 : ℝ) * (1 - ((N + 1 : ℕ) : ℝ)⁻¹) := by
  have htel :
      (∑ n ∈ Finset.range N,
        (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹)) =
        1 - ((N + 1 : ℕ) : ℝ)⁻¹ := by
    simpa [Nat.add_assoc] using
      (Finset.sum_range_sub' (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) N)
  calc
    (∑ n ∈ Finset.range N, telescopingTail n) =
        (1 / 2 : ℝ) * (∑ n ∈ Finset.range N,
          (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹)) := by
      simp_rw [telescopingTail_eq_half_sub]
      rw [Finset.mul_sum]
    _ = (1 / 2 : ℝ) * (1 - ((N + 1 : ℕ) : ℝ)⁻¹) := by rw [htel]

/-- The same partial-sum formula with its exact endpoint denominator displayed. -/
theorem sum_range_telescopingTail (N : ℕ) :
    (∑ n ∈ Finset.range N, telescopingTail n) =
      (1 / 2 : ℝ) - (2 * ((N + 1 : ℕ) : ℝ))⁻¹ := by
  rw [sum_range_telescopingTail_factored]
  simp only [one_div, mul_inv]
  ring

/-- Reciprocal endpoint terms tend to zero; no summability assumption supplies this limit. -/
theorem tendsto_inv_nat_add_one :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Finite telescoping and the reciprocal endpoint limit give convergence to one half. -/
theorem tendsto_sum_range_telescopingTail :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, telescopingTail n)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_nat_add_one
  have hlim := hsub.const_mul (1 / 2 : ℝ)
  simpa only [sub_zero, mul_one, sum_range_telescopingTail_factored] using hlim

/-- Nonnegativity upgrades range-partial-sum convergence to unconditional summation. -/
theorem hasSum_telescopingTail : HasSum telescopingTail (1 / 2 : ℝ) :=
  (hasSum_iff_tendsto_nat_of_nonneg telescopingTail_nonneg (1 / 2 : ℝ)).2
    tendsto_sum_range_telescopingTail

theorem summable_telescopingTail : Summable telescopingTail :=
  hasSum_telescopingTail.summable

/-- The actual telescoping series sums exactly to one half. -/
theorem tsum_telescopingTail_eq_half : (∑' n : ℕ, telescopingTail n) = (1 / 2 : ℝ) :=
  hasSum_telescopingTail.tsum_eq

/-- Summability of the actual inverse-power tail follows from its explicit majorant. -/
theorem summable_inversePower_tail {k : ℕ} (hk : 3 ≤ k) :
    Summable (fun n : ℕ => inversePower k (n + 2)) :=
  Summable.of_nonneg_of_le (fun n => inversePower_nonneg k (n + 2))
    (inversePower_tail_le_telescoping hk) summable_telescopingTail

/-- The actual inverse-power tail is at most one half, without a supplied tail hypothesis. -/
theorem tsum_inversePower_tail_le_half {k : ℕ} (hk : 3 ≤ k) :
    (∑' n : ℕ, inversePower k (n + 2)) ≤ (1 / 2 : ℝ) :=
  hasSum_le (inversePower_tail_le_telescoping hk)
    (summable_inversePower_tail hk).hasSum hasSum_telescopingTail

/-- The shifted index is genuinely equivalent to all natural arguments at least two. -/
def tailIndexEquiv : ℕ ≃ {d : ℕ // 2 ≤ d} where
  toFun n := ⟨n + 2, by omega⟩
  invFun d := d.val - 2
  left_inv n := by
    show n + 2 - 2 = n
    omega
  right_inv d := by
    obtain ⟨d, hd⟩ := d
    apply Subtype.coe_injective
    show d - 2 + 2 = d
    omega

@[simp] theorem tailIndexEquiv_apply_val (n : ℕ) : (tailIndexEquiv n).val = n + 2 := rfl

@[simp] theorem tailIndexEquiv_symm_apply (d : {d : ℕ // 2 ≤ d}) :
    tailIndexEquiv.symm d = d.val - 2 := rfl

/-- Summability is unchanged by the exact tail-index equivalence. -/
theorem summable_inversePower_tail_iff_subtype (k : ℕ) :
    Summable (fun n : ℕ => inversePower k (n + 2)) ↔
      Summable (fun d : {d : ℕ // 2 ≤ d} => inversePower k d.val) := by
  simpa only [Function.comp_def, tailIndexEquiv_apply_val] using
    (tailIndexEquiv.summable_iff
      (f := fun d : {d : ℕ // 2 ≤ d} => inversePower k d.val))

/-- The shifted and subtype-indexed sums are exactly equal. -/
theorem tsum_inversePower_tail_eq_subtype (k : ℕ) :
    (∑' n : ℕ, inversePower k (n + 2)) =
      ∑' d : {d : ℕ // 2 ≤ d}, inversePower k d.val := by
  simpa only [tailIndexEquiv_apply_val] using
    (tailIndexEquiv.tsum_eq (fun d : {d : ℕ // 2 ≤ d} => inversePower k d.val))

/-- Summability on the directly displayed tail d ≥ 2. -/
theorem summable_inversePower_subtype_tail {k : ℕ} (hk : 3 ≤ k) :
    Summable (fun d : {d : ℕ // 2 ≤ d} => inversePower k d.val) :=
  (summable_inversePower_tail_iff_subtype k).1 (summable_inversePower_tail hk)

/-- The directly displayed tail d ≥ 2 has sum at most one half. -/
theorem tsum_inversePower_subtype_tail_le_half {k : ℕ} (hk : 3 ≤ k) :
    (∑' d : {d : ℕ // 2 ≤ d}, inversePower k d.val) ≤ (1 / 2 : ℝ) := by
  rw [← tsum_inversePower_tail_eq_subtype k]
  exact tsum_inversePower_tail_le_half hk

/-- Every finite subfamily of the actual shifted tail satisfies the same bound. -/
theorem sum_inversePower_tail_le_half {k : ℕ} (hk : 3 ≤ k) (s : Finset ℕ) :
    (∑ n ∈ s, inversePower k (n + 2)) ≤ (1 / 2 : ℝ) :=
  ((summable_inversePower_tail hk).sum_le_tsum s
    (fun n _ => inversePower_nonneg k (n + 2))).trans (tsum_inversePower_tail_le_half hk)

end FiniteUnitConvolution

noncomputable section

open scoped BigOperators

namespace FiniteUnitConvolution

universe u v

variable {I : Type u} [Fintype I] [DecidableEq I]

/-- A half-bound on the finite sup norm makes the identity perturbation injective. -/
theorem mulVec_injective_of_half_bound (S : Matrix I I ℂ)
    (hS : ∀ x : I → ℂ, ‖S.mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    Function.Injective (1 + S).mulVec := by
  intro x y hxy
  have hzero : (1 + S).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsum : (x - y) + S.mulVec (x - y) = 0 := by
    simpa only [Matrix.add_mulVec, Matrix.one_mulVec] using hzero
  have hneg : S.mulVec (x - y) = -(x - y) :=
    eq_neg_of_add_eq_zero_right hsum
  have hbound := hS (x - y)
  rw [hneg, norm_neg] at hbound
  apply eq_of_norm_sub_le_zero
  linarith only [hbound]

/-- The identity perturbation is a unit, with no additional invertibility hypothesis. -/
theorem isUnit_one_add_of_half_bound (S : Matrix I I ℂ)
    (hS : ∀ x : I → ℂ, ‖S.mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    IsUnit (1 + S) :=
  (Matrix.mulVec_injective_iff_isUnit (A := 1 + S)).mp
    (mulVec_injective_of_half_bound S hS)

/-- The determinant of the identity perturbation is a unit. -/
theorem isUnit_det_one_add_of_half_bound (S : Matrix I I ℂ)
    (hS : ∀ x : I → ℂ, ‖S.mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    IsUnit (Matrix.det (1 + S)) :=
  (Matrix.isUnit_iff_isUnit_det (1 + S)).mp
    (isUnit_one_add_of_half_bound S hS)

/-- The usual matrix inverse recovers a vector from its identity-perturbation image. -/
theorem recover_one_add_mulVec (S : Matrix I I ℂ)
    (hS : ∀ x : I → ℂ, ‖S.mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖)
    (x : I → ℂ) :
    ((1 + S)⁻¹).mulVec ((1 + S).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul (1 + S) (isUnit_det_one_add_of_half_bound S hS),
    Matrix.one_mulVec]

/-- One fixed inverse matrix supplies the coefficients for every parameter value. -/
theorem coefficients_independent_of_parameter {T : Type v} (S : Matrix I I ℂ)
    (hS : ∀ x : I → ℂ, ‖S.mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖)
    (f p : T → (I → ℂ))
    (hfp : ∀ τ : T, f τ = (1 + S).mulVec (p τ)) :
    ∀ (τ : T) (i : I), p τ i = ∑ j : I, ((1 + S)⁻¹) i j * f τ j := by
  letI : Invertible (1 + S) :=
    Matrix.invertibleOfIsUnitDet (1 + S) (isUnit_det_one_add_of_half_bound S hS)
  intro τ i
  have hrecover : ((1 + S)⁻¹).mulVec (f τ) = p τ :=
    Matrix.inv_mulVec_eq_vec (hfp τ)
  calc
    p τ i = (((1 + S)⁻¹).mulVec (f τ)) i := (congrFun hrecover i).symm
    _ = ∑ j : I, ((1 + S)⁻¹) i j * f τ j := Matrix.mulVec_apply_eq_sum _ _ _

end FiniteUnitConvolution

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

namespace FiniteUnitConvolution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual displayed complex inverse power. -/
def complexInversePower (k d : ℕ) : ℂ := ((d : ℂ) ^ k)⁻¹

lemma norm_complexInversePower (k d : ℕ) :
    ‖complexInversePower k d‖ = ((d : ℝ) ^ k)⁻¹ := by
  simp only [complexInversePower, norm_inv, Complex.norm_pow, Complex.norm_natCast]

lemma realInversePower_nonneg (k d : ℕ) : 0 ≤ ((d : ℝ) ^ k)⁻¹ :=
  inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg d) k)

/-- Each nonzero row summand uses one coordinate of an actual permutation. -/
def permutationTailEntry (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) (i j : I) (n : ℕ) : ℂ :=
  if guard (n + 2) ∧ j = σ (n + 2) i then
    complexInversePower k (n + 2) else 0

/-- The matrix starts at the exact tail boundary d = 2. -/
def permutationTailMatrix (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) : Matrix I I ℂ :=
  Matrix.of fun i j => ∑' n : ℕ, permutationTailEntry k σ guard i j n

lemma norm_permutationTailEntry_le (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) (i j : I) (n : ℕ) :
    ‖permutationTailEntry k σ guard i j n‖ ≤ (((n + 2 : ℕ) : ℝ) ^ k)⁻¹ := by
  unfold permutationTailEntry
  split_ifs with h
  · exact (norm_complexInversePower k (n + 2)).le
  · simpa only [norm_zero] using realInversePower_nonneg k (n + 2)

/-- Entrywise absolute summability follows by direct comparison. -/
theorem summable_permutationTailEntry_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (i j : I) :
    Summable (fun n : ℕ => permutationTailEntry k σ guard i j n) :=
  hpower.of_norm_bounded (norm_permutationTailEntry_le k σ guard i j)

lemma norm_guardedOrbitTerm_le (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) (x : I → ℂ) (i : I) (n : ℕ) :
    ‖(if guard (n + 2) then
      complexInversePower k (n + 2) * x (σ (n + 2) i) else 0 : ℂ)‖ ≤
        (((n + 2 : ℕ) : ℝ) ^ k)⁻¹ * ‖x‖ := by
  by_cases hg : guard (n + 2)
  · simp only [if_pos hg, norm_mul, norm_complexInversePower]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x (σ (n + 2) i))
      (realInversePower_nonneg k (n + 2))
  · simp only [if_neg hg, norm_zero]
    exact mul_nonneg (realInversePower_nonneg k (n + 2)) (norm_nonneg x)

/-- The actual guarded coordinate series is absolutely summable. -/
theorem summable_guardedOrbitTail_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) (i : I) :
    Summable (fun n : ℕ => if guard (n + 2) then
      complexInversePower k (n + 2) * x (σ (n + 2) i) else 0) :=
  (hpower.mul_right ‖x‖).of_norm_bounded (norm_guardedOrbitTerm_le k σ guard x i)

/-- The matrix action is the literal single-coordinate permutation-convolution. -/
theorem permutationTailMatrix_mulVec_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    (permutationTailMatrix k σ guard).mulVec x =
      fun i => ∑' n : ℕ, if guard (n + 2) then
        complexInversePower k (n + 2) * x (σ (n + 2) i) else 0 := by
  funext i
  change (∑ j : I, (∑' n : ℕ, permutationTailEntry k σ guard i j n) * x j) = _
  calc
    (∑ j : I, (∑' n : ℕ, permutationTailEntry k σ guard i j n) * x j) =
        ∑' n : ℕ, ∑ j : I, permutationTailEntry k σ guard i j n * x j := by
      simpa only [tsum_mul_right] using
        (Summable.tsum_finsetSum (s := Finset.univ)
          (f := fun j n => permutationTailEntry k σ guard i j n * x j)
          (fun j _ => (summable_permutationTailEntry_of_power k hpower σ guard i j).mul_right (x j))).symm
    _ = ∑' n : ℕ, if guard (n + 2) then
        complexInversePower k (n + 2) * x (σ (n + 2) i) else 0 := by
      apply tsum_congr
      intro n
      by_cases hg : guard (n + 2)
      · simp [permutationTailEntry, hg, ite_mul]
      · simp [permutationTailEntry, hg]

/-- Finite sup-norm estimate from the explicit scalar tail, with no cardinality loss. -/
theorem norm_permutationTailMatrix_mulVec_le_half_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (htail : (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ k)⁻¹) ≤ (1 / 2 : ℝ))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    ‖(permutationTailMatrix k σ guard).mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg x))).2
  intro i
  rw [permutationTailMatrix_mulVec_of_power k hpower σ guard x]
  change ‖∑' n : ℕ, if guard (n + 2) then
    complexInversePower k (n + 2) * x (σ (n + 2) i) else 0‖ ≤ _
  calc
    ‖∑' n : ℕ, if guard (n + 2) then
      complexInversePower k (n + 2) * x (σ (n + 2) i) else 0‖ ≤
        (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ k)⁻¹) * ‖x‖ :=
      tsum_of_norm_bounded (hpower.hasSum.mul_right ‖x‖)
        (norm_guardedOrbitTerm_le k σ guard x i)
    _ ≤ (1 / 2 : ℝ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right htail (norm_nonneg x)

/-- Identity plus the actual guarded permutation tail. -/
def unitConvolutionMatrix (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) : Matrix I I ℂ :=
  1 + permutationTailMatrix k σ guard

/-- The d = 1 identity contribution is separated from the d ≥ 2 tail. -/
theorem unitConvolutionMatrix_mulVec_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    (unitConvolutionMatrix k σ guard).mulVec x =
      fun i => x i + ∑' n : ℕ, if guard (n + 2) then
        complexInversePower k (n + 2) * x (σ (n + 2) i) else 0 := by
  rw [unitConvolutionMatrix, Matrix.add_mulVec, Matrix.one_mulVec,
    permutationTailMatrix_mulVec_of_power k hpower σ guard x]
  rfl

end FiniteUnitConvolution

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

namespace FiniteUnitConvolution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Literal entries of the identity plus the displayed d ≥ 2 tail. -/
theorem unitConvolutionMatrix_apply (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) (i j : I) :
    unitConvolutionMatrix k σ guard i j =
      (if i = j then (1 : ℂ) else 0) +
        ∑' n : ℕ, if guard (n + 2) ∧ j = σ (n + 2) i then
          (((n + 2 : ℕ) : ℂ) ^ k)⁻¹ else 0 := by
  simp only [unitConvolutionMatrix, Matrix.add_apply, Matrix.one_apply,
    permutationTailMatrix, Matrix.of_apply, permutationTailEntry, complexInversePower]

/-- The genuinely positive-index orbit series is summable from the actual power tail. -/
theorem summable_positiveOrbitSeries_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) (i : I) :
    Summable (fun n : ℕ => if guard (n + 1) then
      complexInversePower k (n + 1) * x (σ (n + 1) i) else 0) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_assoc] using summable_guardedOrbitTail_of_power k hpower σ guard x i

/-- The literal full positive-index row action, with an explicitly justified identity term. -/
theorem unitConvolutionMatrix_mulVec_eq_positive_series_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (hguardOne : guard 1) (hσOne : σ 1 = Equiv.refl I) (x : I → ℂ) :
    (unitConvolutionMatrix k σ guard).mulVec x =
      fun i => ∑' n : ℕ, if guard (n + 1) then
        (((n + 1 : ℕ) : ℂ) ^ k)⁻¹ * x (σ (n + 1) i) else 0 := by
  rw [unitConvolutionMatrix_mulVec_of_power k hpower σ guard x]
  funext i
  have hs := summable_positiveOrbitSeries_of_power k hpower σ guard x i
  have he := hs.tsum_eq_zero_add
  simpa only [Nat.zero_add, hguardOne, ite_eq_left, hσOne, Equiv.refl_apply,
    complexInversePower, Nat.cast_one, one_pow, inv_one, one_mul, Nat.add_assoc] using he.symm

/-- Positive-index entries, including the first term, are absolutely summable. -/
theorem summable_positivePermutationEntry_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (i j : I) :
    Summable (fun n : ℕ => if guard (n + 1) ∧ j = σ (n + 1) i then
      complexInversePower k (n + 1) else 0) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_assoc, permutationTailEntry] using
    summable_permutationTailEntry_of_power k hpower σ guard i j

/-- The full positive-index matrix agrees with the identity-plus-tail matrix under exact head data. -/
theorem unitConvolutionMatrix_eq_positive_series_of_power (k : ℕ)
    (hpower : Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹))
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (hguardOne : guard 1) (hσOne : σ 1 = Equiv.refl I) :
    unitConvolutionMatrix k σ guard = Matrix.of (fun i j =>
      ∑' n : ℕ, if guard (n + 1) ∧ j = σ (n + 1) i then
        (((n + 1 : ℕ) : ℂ) ^ k)⁻¹ else 0) := by
  ext i j
  have hs := summable_positivePermutationEntry_of_power k hpower σ guard i j
  have he := hs.tsum_eq_zero_add
  rw [unitConvolutionMatrix_apply]
  simpa only [Matrix.of_apply, Nat.zero_add, hguardOne, true_and, hσOne,
    Equiv.refl_apply, complexInversePower, Nat.cast_one, one_pow, inv_one,
    Nat.add_assoc, eq_comm] using he.symm

end FiniteUnitConvolution

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

namespace FiniteUnitConvolution

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Actual summability of the displayed scalar inverse-power tail. -/
theorem summable_displayedInversePower_tail {k : ℕ} (hk : 3 ≤ k) :
    Summable (fun n : ℕ => (((n + 2 : ℕ) : ℝ) ^ k)⁻¹) := by
  simpa only [inversePower] using summable_inversePower_tail hk

/-- Actual one-half bound for the displayed scalar inverse-power tail. -/
theorem tsum_displayedInversePower_tail_le_half {k : ℕ} (hk : 3 ≤ k) :
    (∑' n : ℕ, (((n + 2 : ℕ) : ℝ) ^ k)⁻¹) ≤ (1 / 2 : ℝ) := by
  simpa only [inversePower] using tsum_inversePower_tail_le_half hk

/-- Concrete guarded matrix entries are absolutely summable for every k ≥ 3. -/
theorem summable_permutationTailEntry (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (i j : I) :
    Summable (fun n : ℕ => permutationTailEntry k σ guard i j n) :=
  summable_permutationTailEntry_of_power k (summable_displayedInversePower_tail hk)
    σ guard i j

/-- Concrete guarded orbit terms are absolutely summable for every k ≥ 3. -/
theorem summable_guardedOrbitTail (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) (i : I) :
    Summable (fun n : ℕ => if guard (n + 2) then
      complexInversePower k (n + 2) * x (σ (n + 2) i) else 0) :=
  summable_guardedOrbitTail_of_power k (summable_displayedInversePower_tail hk)
    σ guard x i

/-- The concrete matrix has exactly the claimed permutation-convolution action. -/
theorem permutationTailMatrix_mulVec (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    (permutationTailMatrix k σ guard).mulVec x =
      fun i => ∑' n : ℕ, if guard (n + 2) then
        complexInversePower k (n + 2) * x (σ (n + 2) i) else 0 :=
  permutationTailMatrix_mulVec_of_power k (summable_displayedInversePower_tail hk)
    σ guard x

/-- Concrete one-half contraction: no summability, tail, or norm-bound premise is supplied. -/
theorem norm_permutationTailMatrix_mulVec_le_half (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    ‖(permutationTailMatrix k σ guard).mulVec x‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
  norm_permutationTailMatrix_mulVec_le_half_of_power k
    (summable_displayedInversePower_tail hk) (tsum_displayedInversePower_tail_le_half hk)
    σ guard x

/-- The concrete identity-plus-tail matrix is injective for every finite index type. -/
theorem unitConvolution_injective (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    Function.Injective (unitConvolutionMatrix k σ guard).mulVec :=
  mulVec_injective_of_half_bound (permutationTailMatrix k σ guard)
    (norm_permutationTailMatrix_mulVec_le_half k hk σ guard)

/-- Concrete invertibility is produced from the actual inverse-power contraction. -/
theorem unitConvolution_isUnit (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    IsUnit (unitConvolutionMatrix k σ guard) :=
  (Matrix.mulVec_injective_iff_isUnit (A := unitConvolutionMatrix k σ guard)).mp
    (unitConvolution_injective k hk σ guard)

/-- The actual determinant is a unit, not a separate inverse assumption. -/
theorem unitConvolution_det_isUnit (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    IsUnit (unitConvolutionMatrix k σ guard).det :=
  (Matrix.isUnit_iff_isUnit_det (unitConvolutionMatrix k σ guard)).mp
    (unitConvolution_isUnit k hk σ guard)

/-- The usual adjugate/determinant inverse is a genuine left inverse. -/
theorem unitConvolution_nonsing_inv_mul (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    (unitConvolutionMatrix k σ guard)⁻¹ * unitConvolutionMatrix k σ guard = 1 :=
  Matrix.nonsing_inv_mul _ (unitConvolution_det_isUnit k hk σ guard)

/-- The same usual matrix inverse is a genuine right inverse. -/
theorem unitConvolution_mul_nonsing_inv (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    unitConvolutionMatrix k σ guard * (unitConvolutionMatrix k σ guard)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (unitConvolution_det_isUnit k hk σ guard)

/-- The concrete usual inverse recovers any vector from its concrete convolution image. -/
theorem unitConvolution_inv_mulVec (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) :
    ((unitConvolutionMatrix k σ guard)⁻¹).mulVec
      ((unitConvolutionMatrix k σ guard).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, unitConvolution_nonsing_inv_mul k hk σ guard,
    Matrix.one_mulVec]

/-- Literal recovery through the standard inverse-vector API. -/
theorem unitConvolution_recover (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) {u v : I → ℂ}
    (h : u = (unitConvolutionMatrix k σ guard).mulVec v) :
    ((unitConvolutionMatrix k σ guard)⁻¹).mulVec u = v := by
  letI : Invertible (unitConvolutionMatrix k σ guard) :=
    Matrix.invertibleOfIsUnitDet _ (unitConvolution_det_isUnit k hk σ guard)
  exact Matrix.inv_mulVec_eq_vec h

/-- Coefficients are entries of the actual matrix inverse and have no parameter argument. -/
def unitConvolutionInverseCoefficients (k : ℕ) (σ : ℕ → Equiv.Perm I)
    (guard : ℕ → Prop) : Matrix I I ℂ :=
  (unitConvolutionMatrix k σ guard)⁻¹

/-- One fixed finite inverse gives constant coefficients for an entire parameterized family. -/
theorem unitConvolution_coefficients_independent_of_parameter {T : Type*}
    (k : ℕ) (hk : 3 ≤ k) (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (f p : T → (I → ℂ))
    (hfp : ∀ τ : T, f τ = (unitConvolutionMatrix k σ guard).mulVec (p τ)) :
    ∀ (τ : T) (i : I), p τ i =
      ∑ j : I, unitConvolutionInverseCoefficients k σ guard i j * f τ j := by
  intro τ i
  have hr := unitConvolution_recover k hk σ guard (hfp τ)
  calc
    p τ i = (((unitConvolutionMatrix k σ guard)⁻¹).mulVec (f τ)) i :=
      (congrFun hr i).symm
    _ = ∑ j : I, unitConvolutionInverseCoefficients k σ guard i j * f τ j :=
      Matrix.mulVec_apply_eq_sum _ _ _

/-- Existential constant coefficients with all concrete summability and bounds discharged. -/
theorem unitConvolution_exists_constant_coefficients {T : Type*}
    (k : ℕ) (hk : 3 ≤ k) (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (f p : T → (I → ℂ))
    (hfp : ∀ τ : T, f τ = (unitConvolutionMatrix k σ guard).mulVec (p τ)) :
    ∃ C : Matrix I I ℂ, ∀ (τ : T) (i : I), p τ i = ∑ j : I, C i j * f τ j :=
  ⟨unitConvolutionInverseCoefficients k σ guard,
    unitConvolution_coefficients_independent_of_parameter k hk σ guard f p hfp⟩

/-- The actual coprime guard is a specialization, with no invertibility premise. -/
theorem coprime_unitConvolution_isUnit (N k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) :
    IsUnit (unitConvolutionMatrix k σ (fun d => Nat.Coprime d N)) :=
  unitConvolution_isUnit k hk σ (fun d => Nat.Coprime d N)

/-- The empty index type has determinant one, even though its matrices are subsingletons. -/
theorem unitConvolution_det_empty [IsEmpty I] (k : ℕ)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) :
    (unitConvolutionMatrix k σ guard).det = 1 :=
  Matrix.det_isEmpty

/-- The positive-index row series is genuinely summable in the concrete range k ≥ 3. -/
theorem summable_positiveOrbitSeries (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop) (x : I → ℂ) (i : I) :
    Summable (fun n : ℕ => if guard (n + 1) then
      complexInversePower k (n + 1) * x (σ (n + 1) i) else 0) :=
  summable_positiveOrbitSeries_of_power k (summable_displayedInversePower_tail hk)
    σ guard x i

/-- A full positive-index action is identified only after its exact identity data are supplied. -/
theorem unitConvolutionMatrix_mulVec_eq_positive_series (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (hguardOne : guard 1) (hσOne : σ 1 = Equiv.refl I) (x : I → ℂ) :
    (unitConvolutionMatrix k σ guard).mulVec x =
      fun i => ∑' n : ℕ, if guard (n + 1) then
        (((n + 1 : ℕ) : ℂ) ^ k)⁻¹ * x (σ (n + 1) i) else 0 :=
  unitConvolutionMatrix_mulVec_eq_positive_series_of_power k
    (summable_displayedInversePower_tail hk) σ guard hguardOne hσOne x

/-- The concrete matrix is the full positive-index coefficient series with exact head data. -/
theorem unitConvolutionMatrix_eq_positive_series (k : ℕ) (hk : 3 ≤ k)
    (σ : ℕ → Equiv.Perm I) (guard : ℕ → Prop)
    (hguardOne : guard 1) (hσOne : σ 1 = Equiv.refl I) :
    unitConvolutionMatrix k σ guard = Matrix.of (fun i j =>
      ∑' n : ℕ, if guard (n + 1) ∧ j = σ (n + 1) i then
        (((n + 1 : ℕ) : ℂ) ^ k)⁻¹ else 0) :=
  unitConvolutionMatrix_eq_positive_series_of_power k
    (summable_displayedInversePower_tail hk) σ guard hguardOne hσOne

end FiniteUnitConvolution
