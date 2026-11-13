import Submission.Hypergraph.HierarchicalGoodAtoms
import Submission.Hypergraph.TowerDominatingGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite hierarchical parameter selection

The good-atom layer reduces the dense removal parameters to two finite
inequalities.  This file solves their non-circular numerical core.

For an a priori complexity window `M ≤ B`, use the floored growth function

```
F_Q(M) = max Q (M + 1).
```

Once `B + 1 ≤ Q`, every value in that window is literally `Q`.  Hence

```
τ = 1 / Q,          ρ = 1 / log Q,
```

at every selected rank.  Mathlib's asymptotic theorem
`log(x)^N = o(sqrt x)` then gives a concrete sufficiently large natural
`Q` for which

```
N * (sqrt τ + B * τ) < ρ^N.
```

At the same time `ρ → 0`, so the low-density cleaning cost is small.
An explicit positive `γ(Q)` pays for all energy-gap terms.

The final section applies the scalar choice uniformly to arbitrary finite
rank vectors whose selected lower and adjacent upper complexities lie in
the window.  The residual obstruction is therefore isolated precisely:
one still has to construct a regularity certificate whose selected
complexities lie in a bound chosen before `Q`, or replace the single-window
construction by Tao's rank-by-rank preselected hierarchy.
-/

namespace Submission.GreenTao

open scoped BigOperators Topology
open Filter

/-! ## A growth function constant on a prescribed finite window -/

/-- A monotone growth function with a freely chosen floor. -/
def flooredGrowth (Q : ℕ) : NatGrowthFunction where
  toFun M := max Q (M + 1)
  monotone' := by
    intro a b hab
    exact max_le_max le_rfl (Nat.add_le_add_right hab 1)
  above_diagonal := by
    intro M
    exact le_max_right _ _

@[simp]
theorem flooredGrowth_apply (Q M : ℕ) :
    flooredGrowth Q M = max Q (M + 1) :=
  rfl

/-- Above the whole window `0, ..., B`, the floored growth function is
literally constant. -/
theorem flooredGrowth_eq_floor
    {Q B M : ℕ} (hM : M ≤ B) (hQ : B + 1 ≤ Q) :
    flooredGrowth Q M = Q := by
  rw [flooredGrowth_apply, max_eq_left]
  exact (Nat.add_le_add_right hM 1).trans hQ

/-! ## Common scalar parameters -/

/-- Common reciprocal tolerance at growth floor `Q`. -/
noncomputable def hierarchicalCommonTolerance (Q : ℕ) : ℝ :=
  1 / (Q : ℝ)

/-- Common logarithmic density floor at growth floor `Q`. -/
noncomputable def hierarchicalCommonDensityFloor (Q : ℕ) : ℝ :=
  1 / Real.log (Q : ℝ)

/-- Common elementary square-root defect error. -/
noncomputable def hierarchicalCommonDefectError (Q : ℕ) : ℝ :=
  Real.sqrt (hierarchicalCommonTolerance Q)

/-- Explicit positive gap target reserving half the deletion allowance for
all energy-gap terms. -/
noncomputable def hierarchicalCommonGap
    (subfaceCount complexityBound Q : ℕ) (ξ : ℝ) : ℝ :=
  ξ /
    (2 *
      ((subfaceCount : ℝ) + 1) *
      ((complexityBound : ℝ) + 1) *
      (Q : ℝ))

theorem hierarchicalCommonTolerance_pos
    {Q : ℕ} (hQ : 0 < Q) :
    0 < hierarchicalCommonTolerance Q := by
  unfold hierarchicalCommonTolerance
  positivity

theorem hierarchicalCommonDensityFloor_pos
    {Q : ℕ} (hQ : 1 < Q) :
    0 < hierarchicalCommonDensityFloor Q := by
  unfold hierarchicalCommonDensityFloor
  exact one_div_pos.mpr
    (Real.log_pos (by exact_mod_cast hQ))

theorem hierarchicalCommonDefectError_nonneg
    (Q : ℕ) :
    0 ≤ hierarchicalCommonDefectError Q :=
  Real.sqrt_nonneg _

theorem hierarchicalCommonGap_pos
    {subfaceCount complexityBound Q : ℕ}
    {ξ : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q) :
    0 <
      hierarchicalCommonGap
        subfaceCount complexityBound Q ξ := by
  unfold hierarchicalCommonGap
  positivity

/-! ## Scalar asymptotics -/

/-- The logarithmic density floor tends to zero along natural growth
values. -/
theorem tendsto_hierarchicalCommonDensityFloor :
    Tendsto hierarchicalCommonDensityFloor atTop (𝓝 0) := by
  unfold hierarchicalCommonDensityFloor
  simpa [one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)

/-- `log(Q)^N / sqrt(Q)` tends to zero along natural `Q`. -/
theorem tendsto_pow_log_div_sqrt_nat (N : ℕ) :
    Tendsto
      (fun Q : ℕ =>
        Real.log (Q : ℝ) ^ N / Real.sqrt (Q : ℝ))
      atTop (𝓝 0) := by
  have hreal :
      Tendsto
        (fun x : ℝ =>
          Real.log x ^ N / Real.sqrt x)
        atTop (𝓝 0) := by
    have hsqrt :=
      (Real.isLittleO_pow_log_id_atTop (n := N)).comp_tendsto
        Real.tendsto_sqrt_atTop
    have hbase :
        Tendsto
          (fun x : ℝ =>
            Real.log (Real.sqrt x) ^ N /
              Real.sqrt x)
          atTop (𝓝 0) :=
      hsqrt.tendsto_div_nhds_zero
    have hscaled :
        Tendsto
          (fun x : ℝ =>
            (2 : ℝ) ^ N *
              (Real.log (Real.sqrt x) ^ N /
                Real.sqrt x))
          atTop (𝓝 0) := by
      simpa using hbase.const_mul ((2 : ℝ) ^ N)
    refine hscaled.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_sqrt hx.le]
    have hsqrt : Real.sqrt x ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hx)
    field_simp
    rw [← mul_pow]
    congr 1
    ring
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- The square-root reciprocal error times `log(Q)^N` tends to zero. -/
theorem tendsto_sqrt_inv_mul_pow_log_nat (N : ℕ) :
    Tendsto
      (fun Q : ℕ =>
        Real.sqrt (1 / (Q : ℝ)) *
          Real.log (Q : ℝ) ^ N)
      atTop (𝓝 0) := by
  refine (tendsto_pow_log_div_sqrt_nat N).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with Q hQ
  have hQReal : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast hQ
  rw [one_div, Real.sqrt_inv]
  field_simp

/-- The reciprocal error times `log(Q)^N` also tends to zero. -/
theorem tendsto_inv_mul_pow_log_nat (N : ℕ) :
    Tendsto
      (fun Q : ℕ =>
        (1 / (Q : ℝ)) * Real.log (Q : ℝ) ^ N)
      atTop (𝓝 0) := by
  have hbase :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      1 0 N one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using
    hbase

/-- The complete scalar counting-error ratio tends to zero. -/
theorem tendsto_hierarchicalCountingRatio
    (faceCount complexityBound : ℕ) :
    Tendsto
      (fun Q : ℕ =>
        (faceCount : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) *
          Real.log (Q : ℝ) ^ faceCount)
      atTop (𝓝 0) := by
  have hsqrt :=
    tendsto_sqrt_inv_mul_pow_log_nat faceCount
  have hinv :=
    (tendsto_inv_mul_pow_log_nat faceCount).const_mul
      (complexityBound : ℝ)
  have hmul :
      Tendsto
        (fun Q : ℕ =>
          (faceCount : ℝ) *
            (Real.sqrt (1 / (Q : ℝ)) *
                Real.log (Q : ℝ) ^ faceCount +
              (complexityBound : ℝ) *
                ((1 / (Q : ℝ)) *
                  Real.log (Q : ℝ) ^ faceCount)))
        atTop (𝓝 0) := by
    simpa using (hsqrt.add hinv).const_mul (faceCount : ℝ)
  refine hmul.congr' ?_
  filter_upwards with Q
  simp only [hierarchicalCommonDefectError,
    hierarchicalCommonTolerance]
  ring

/-! ## Existence of one common finite scale -/

/-- A sufficiently large common growth value simultaneously makes the
low-density cleaning cost small and the mixed-count error smaller than the
product of logarithmic density floors. -/
theorem exists_hierarchicalCommonScale
    (faceCount subfaceCount complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ Q : ℕ,
      complexityBound + 2 ≤ Q ∧
      (subfaceCount : ℝ) *
          (complexityBound : ℝ) *
          hierarchicalCommonDensityFloor Q <
        ξ / 2 ∧
      (faceCount : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) <
        hierarchicalCommonDensityFloor Q ^ faceCount := by
  have hclean :
      Tendsto
        (fun Q : ℕ =>
          (subfaceCount : ℝ) *
            (complexityBound : ℝ) *
            hierarchicalCommonDensityFloor Q)
        atTop (𝓝 0) := by
    simpa using
      tendsto_hierarchicalCommonDensityFloor.const_mul
        ((subfaceCount : ℝ) * (complexityBound : ℝ))
  have hcleanEventually :
      ∀ᶠ Q : ℕ in atTop,
        (subfaceCount : ℝ) *
            (complexityBound : ℝ) *
            hierarchicalCommonDensityFloor Q <
          ξ / 2 :=
    hclean.eventually_lt_const (half_pos hξ)
  have hratioEventually :
      ∀ᶠ Q : ℕ in atTop,
        (faceCount : ℝ) *
            (hierarchicalCommonDefectError Q +
              (complexityBound : ℝ) *
                hierarchicalCommonTolerance Q) *
            Real.log (Q : ℝ) ^ faceCount <
          1 :=
    (tendsto_hierarchicalCountingRatio
      faceCount complexityBound).eventually_lt_const
        zero_lt_one
  obtain ⟨Q, hQlarge, hQclean, hQratio⟩ :=
    ((eventually_ge_atTop (complexityBound + 2)).and
      (hcleanEventually.and hratioEventually)).exists
  refine ⟨Q, hQlarge, hQclean, ?_⟩
  have hQtwo : 1 < Q := by omega
  have hlog : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast hQtwo)
  rw [hierarchicalCommonDensityFloor, one_div_pow]
  exact (lt_div_iff₀ (pow_pos hlog faceCount)).2
    hQratio

/-! ## Paying for all energy gaps -/

/-- Dividing the explicit energy gap by the reciprocal tolerance cancels
the growth value exactly. -/
theorem hierarchicalCommonGap_div_tolerance
    {subfaceCount complexityBound Q : ℕ}
    {ξ : ℝ} (hQ : 0 < Q) :
    hierarchicalCommonGap
          subfaceCount complexityBound Q ξ /
        hierarchicalCommonTolerance Q =
      ξ /
        (2 *
          ((subfaceCount : ℝ) + 1) *
          ((complexityBound : ℝ) + 1)) := by
  unfold hierarchicalCommonGap hierarchicalCommonTolerance
  have hQReal : (Q : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hQ)
  field_simp

/-- The explicit gap schedule spends at most half the deletion allowance,
even after multiplying by all subfaces and the full complexity window. -/
theorem hierarchicalCommonGap_cost_le_half
    (subfaceCount complexityBound Q : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q) :
    (subfaceCount : ℝ) *
          (complexityBound : ℝ) *
          (hierarchicalCommonGap
              subfaceCount complexityBound Q ξ /
            hierarchicalCommonTolerance Q) ≤
      ξ / 2 := by
  rw [hierarchicalCommonGap_div_tolerance hQ]
  have hsnonneg : (0 : ℝ) ≤ subfaceCount := Nat.cast_nonneg _
  have hbnonneg : (0 : ℝ) ≤ complexityBound := Nat.cast_nonneg _
  have hdenpos :
      0 <
        ((subfaceCount : ℝ) + 1) *
          ((complexityBound : ℝ) + 1) := by
    positivity
  have hprod :
      (subfaceCount : ℝ) * (complexityBound : ℝ) ≤
        ((subfaceCount : ℝ) + 1) *
          ((complexityBound : ℝ) + 1) := by
    exact mul_le_mul
      (by linarith) (by linarith)
      hbnonneg (by positivity)
  calc
    (subfaceCount : ℝ) *
          (complexityBound : ℝ) *
          (ξ /
            (2 *
              ((subfaceCount : ℝ) + 1) *
              ((complexityBound : ℝ) + 1))) =
        (ξ / 2) *
          (((subfaceCount : ℝ) *
              (complexityBound : ℝ)) /
            (((subfaceCount : ℝ) + 1) *
              ((complexityBound : ℝ) + 1))) := by
      field_simp
    _ ≤ (ξ / 2) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact (div_le_one hdenpos).2 hprod
      · exact (half_pos hξ).le
    _ = ξ / 2 := by ring

/-- A common scale together with its explicit positive gap simultaneously
pays for both kinds of deletion terms and the complete mixed-count error. -/
theorem exists_hierarchicalCommonScale_with_gap
    (faceCount subfaceCount complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ Q : ℕ,
      complexityBound + 2 ≤ Q ∧
      0 <
        hierarchicalCommonGap
          subfaceCount complexityBound Q ξ ∧
      (subfaceCount : ℝ) *
          (complexityBound : ℝ) *
          hierarchicalCommonDensityFloor Q <
        ξ / 2 ∧
      (subfaceCount : ℝ) *
          (complexityBound : ℝ) *
          (hierarchicalCommonGap
              subfaceCount complexityBound Q ξ /
            hierarchicalCommonTolerance Q) ≤
        ξ / 2 ∧
      (faceCount : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) <
        hierarchicalCommonDensityFloor Q ^ faceCount := by
  obtain ⟨Q, hQlarge, hclean, hcount⟩ :=
    exists_hierarchicalCommonScale
      faceCount subfaceCount complexityBound hξ
  have hQpos : 0 < Q := by omega
  exact ⟨Q, hQlarge,
    hierarchicalCommonGap_pos hξ hQpos,
    hclean,
    hierarchicalCommonGap_cost_le_half
      subfaceCount complexityBound Q hξ hQpos,
    hcount⟩

/-! ## Uniform finite sums and products -/

/-- The scalar counting inequality is exactly the finite constant-vector
inequality.  This is the numerical diagonal needed for every selected
positive-face vector of the prescribed cardinality. -/
theorem finite_commonCountingError_lt_densityProduct
    {α : Type*} [Fintype α]
    (complexityBound Q : ℕ)
    (hcount :
      (Fintype.card α : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) <
        hierarchicalCommonDensityFloor Q ^
          Fintype.card α) :
    (∑ _ : α,
        (hierarchicalCommonDefectError Q +
          (complexityBound : ℝ) *
            hierarchicalCommonTolerance Q)) <
      ∏ _ : α, hierarchicalCommonDensityFloor Q := by
  simpa [mul_add] using hcount

/-- The two half-budget estimates imply the constant-vector deletion
budget. -/
theorem finite_commonCleaningBudget_lt
    {α : Type*} [Fintype α]
    (complexityBound Q : ℕ)
    {ξ : ℝ}
    (hclean :
      (Fintype.card α : ℝ) *
          (complexityBound : ℝ) *
          hierarchicalCommonDensityFloor Q <
        ξ / 2)
    (hgap :
      (Fintype.card α : ℝ) *
          (complexityBound : ℝ) *
          (hierarchicalCommonGap
              (Fintype.card α) complexityBound Q ξ /
            hierarchicalCommonTolerance Q) ≤
        ξ / 2) :
    (∑ _ : α,
        ((complexityBound : ℝ) *
            hierarchicalCommonDensityFloor Q +
          ((complexityBound : ℝ) *
              hierarchicalCommonGap
                (Fintype.card α) complexityBound Q ξ) /
            hierarchicalCommonTolerance Q)) <
      ξ := by
  rw [Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have htotal :
      (Fintype.card α : ℝ) *
            (complexityBound : ℝ) *
            hierarchicalCommonDensityFloor Q +
          (Fintype.card α : ℝ) *
            (complexityBound : ℝ) *
            (hierarchicalCommonGap
                (Fintype.card α) complexityBound Q ξ /
              hierarchicalCommonTolerance Q) <
        ξ := by
    linarith
  convert htotal using 1
  ring

/-! ## Transfer to selected regularity certificates -/

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- If every selected lower complexity lies in the preselected window,
then the literal selected growth value is the common scale `Q`. -/
theorem selectedRankGrowthValue_eq_common_of_window
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q)
    (j : Fin r) :
    R.selectedRankGrowthValue j = Q := by
  unfold selectedRankGrowthValue
  exact flooredGrowth_eq_floor
    (hcoarseWindow j) hQ

/-- The selected reciprocal tolerance is constant on the complexity
window. -/
theorem selectedRankTolerance_eq_common_of_window
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q)
    (j : Fin r) :
    R.selectedRankTolerance j =
      hierarchicalCommonTolerance Q := by
  unfold selectedRankTolerance hierarchicalCommonTolerance
  rw [R.selectedRankGrowthValue_eq_common_of_window
    hcoarseWindow hQ j]

/-- The selected logarithmic density floor is constant on the complexity
window. -/
theorem selectedRankDensityFloor_eq_common_of_window
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q)
    (j : Fin r) :
    R.selectedRankDensityFloor j =
      hierarchicalCommonDensityFloor Q := by
  unfold selectedRankDensityFloor
    hierarchicalCommonDensityFloor
  rw [R.selectedRankGrowthValue_eq_common_of_window
    hcoarseWindow hQ j]

/-- The selected square-root defect error is constant on the complexity
window. -/
theorem selectedRankDefectError_eq_common_of_window
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q)
    (j : Fin r) :
    R.selectedRankDefectError j =
      hierarchicalCommonDefectError Q := by
  unfold selectedRankDefectError
    hierarchicalCommonDefectError
  rw [R.selectedRankTolerance_eq_common_of_window
    hcoarseWindow hQ j]

/-- Under the preselected lower-complexity window and the adjacent
fine-upper window, the scalar inequality controls the literal selected
finite rank vector used by mixed configuration counting. -/
theorem selectedCountingError_lt_densityProduct_of_window
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hfineUpperWindow :
      ∀ j : Fin r,
        R.selectedFineUpperComplexityBound j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q)
    (hcount :
      (Fintype.card (PositiveOrderedFace k r) : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) <
        hierarchicalCommonDensityFloor Q ^
          Fintype.card (PositiveOrderedFace k r)) :
    (∑ e : PositiveOrderedFace k r,
        (R.selectedDefectError e.rank +
          (R.selectedFineUpperComplexityBound
              e.lowerRank : ℝ) *
            R.selectedRankTolerance e.lowerRank)) <
      ∏ e : PositiveOrderedFace k r,
        R.selectedDensityFloor e.rank := by
  have hQpos : 0 < Q := by omega
  calc
    (∑ e : PositiveOrderedFace k r,
        (R.selectedDefectError e.rank +
          (R.selectedFineUpperComplexityBound
              e.lowerRank : ℝ) *
            R.selectedRankTolerance e.lowerRank)) ≤
        ∑ _e : PositiveOrderedFace k r,
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) := by
      apply Finset.sum_le_sum
      intro e _he
      rw [R.selectedDefectError_positiveFace_rank,
        R.selectedRankDefectError_eq_common_of_window
          hcoarseWindow hQ e.lowerRank,
        R.selectedRankTolerance_eq_common_of_window
          hcoarseWindow hQ e.lowerRank]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (hfineUpperWindow e.lowerRank))
          (hierarchicalCommonTolerance_pos hQpos).le)
        _
    _ <
        ∏ _e : PositiveOrderedFace k r,
          hierarchicalCommonDensityFloor Q :=
      finite_commonCountingError_lt_densityProduct
        complexityBound Q hcount
    _ =
        ∏ e : PositiveOrderedFace k r,
          R.selectedDensityFloor e.rank := by
      apply Finset.prod_congr rfl
      intro e _he
      rw [R.selectedDensityFloor_positiveFace_rank]
      exact
        (R.selectedRankDensityFloor_eq_common_of_window
          hcoarseWindow hQ e.lowerRank).symm

/-- Respecting both adjacent upper-complexity bounds, the common gap
schedule controls the literal coarse-cleaning sum. -/
theorem selectedCoarseCleaningSum_lt_of_window
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {complexityBound Q : ℕ}
    {ξ : ℝ} (hξ : 0 < ξ)
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q)
        (fun _ =>
          hierarchicalCommonGap
            (Fintype.card (OrderedPositiveSubface r))
            complexityBound Q ξ))
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hfineUpperWindow :
      ∀ j : Fin r,
        R.selectedFineUpperComplexityBound j ≤
          complexityBound)
    (hcoarseUpperWindow :
      ∀ j : Fin r,
        R.selectedCoarseUpperComplexityBound j ≤
          complexityBound)
    (hQ : complexityBound + 2 ≤ Q)
    (hclean :
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (complexityBound : ℝ) *
          hierarchicalCommonDensityFloor Q <
        ξ / 2) :
    (∑ q : OrderedPositiveSubface r,
        ((R.selectedCoarseUpperComplexityBound q.1 : ℝ) *
            R.selectedRankDensityFloor q.1 +
          ((R.selectedFineUpperComplexityBound q.1 : ℝ) *
              hierarchicalCommonGap
                (Fintype.card (OrderedPositiveSubface r))
                complexityBound Q ξ) /
            R.selectedRankTolerance q.1)) <
      ξ := by
  have hQpos : 0 < Q := by omega
  have hQfloor : complexityBound + 1 ≤ Q := by omega
  calc
    (∑ q : OrderedPositiveSubface r,
        ((R.selectedCoarseUpperComplexityBound q.1 : ℝ) *
            R.selectedRankDensityFloor q.1 +
          ((R.selectedFineUpperComplexityBound q.1 : ℝ) *
              hierarchicalCommonGap
                (Fintype.card (OrderedPositiveSubface r))
                complexityBound Q ξ) /
            R.selectedRankTolerance q.1)) ≤
        ∑ _q : OrderedPositiveSubface r,
          ((complexityBound : ℝ) *
              hierarchicalCommonDensityFloor Q +
            ((complexityBound : ℝ) *
                hierarchicalCommonGap
                  (Fintype.card (OrderedPositiveSubface r))
                  complexityBound Q ξ) /
              hierarchicalCommonTolerance Q) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [R.selectedRankDensityFloor_eq_common_of_window
          hcoarseWindow hQfloor q.1,
        R.selectedRankTolerance_eq_common_of_window
          hcoarseWindow hQfloor q.1]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (hcoarseUpperWindow q.1))
          (hierarchicalCommonDensityFloor_pos
            (by omega : 1 < Q)).le
      · apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr
              (hfineUpperWindow q.1))
            (hierarchicalCommonGap_pos hξ hQpos).le
        · exact
            (hierarchicalCommonTolerance_pos hQpos).le
    _ < ξ := by
      apply finite_commonCleaningBudget_lt
        complexityBound Q hclean
      exact hierarchicalCommonGap_cost_le_half
        (Fintype.card (OrderedPositiveSubface r))
        complexityBound Q hξ hQpos

/-- The preceding numerical bound closes the actual selected coarse
bad-base deletion estimate for every top face. -/
theorem faceDeletionDensity_selectedCoarseBadBase_lt_of_window
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {complexityBound Q : ℕ}
    {ξ : ℝ} (hξ : 0 < ξ)
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q)
        (fun _ =>
          hierarchicalCommonGap
            (Fintype.card (OrderedPositiveSubface r))
            complexityBound Q ξ))
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hfineUpperWindow :
      ∀ j : Fin r,
        R.selectedFineUpperComplexityBound j ≤
          complexityBound)
    (hcoarseUpperWindow :
      ∀ j : Fin r,
        R.selectedCoarseUpperComplexityBound j ≤
          complexityBound)
    (hQ : complexityBound + 2 ≤ Q)
    (hclean :
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (complexityBound : ℝ) *
          hierarchicalCommonDensityFloor Q <
        ξ / 2)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        R.selectedCoarseBadBaseDeletionFamily e <
      ξ := by
  exact
    (R.faceDeletionDensity_selectedCoarseBadBase_le e).trans_lt
      (R.selectedCoarseCleaningSum_lt_of_window
        hξ hcoarseWindow hfineUpperWindow
        hcoarseUpperWindow hQ hclean)

/-- The same finite-window hypotheses make every mixed-good selected
configuration have positive normalized count. -/
theorem mixedFullConfigurationCount_pos_of_window
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hfineUpperWindow :
      ∀ j : Fin r,
        R.selectedFineUpperComplexityBound j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q)
    (hcount :
      (Fintype.card (PositiveOrderedFace k r) : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) <
        hierarchicalCommonDensityFloor Q ^
          Fintype.card (PositiveOrderedFace k r))
    (A : ClosedOrderedAtomConfiguration G k r R.coarse)
    (hgood :
      A.IsMixedGood R.toCoarseFine
        R.selectedDensityFloor
        R.selectedDefectThreshold) :
    0 < fullConfigurationCount A := by
  exact R.mixedFullConfigurationCount_pos_selected
    A hgood
    (R.selectedCountingError_lt_densityProduct_of_window
      hcoarseWindow hfineUpperWindow hQ hcount)

end GrowthFunctionOrderedComplexRegularityCertificate

/-! ## One concrete finite diagonal -/

/-- Choose the floored growth function and explicit positive rank gap
before seeing the regularity certificate.  The choice works uniformly for
every certificate whose selected lower complexities and both adjacent
upper complexities fit the declared finite window.

This is a genuine finite diagonal rather than an assumption interface:
`Q` is obtained from the logarithmic/square-root asymptotics, and the gap
is the displayed formula `ξ / (2 (S+1) (B+1) Q)`. -/
theorem exists_hierarchicalFiniteWindowParameters
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ Q : ℕ,
      complexityBound + 2 ≤ Q ∧
      0 <
        hierarchicalCommonGap
          (Fintype.card (OrderedPositiveSubface r))
          complexityBound Q ξ ∧
      ∀ R : GrowthFunctionOrderedComplexRegularityCertificate
          G k r initial initialBound (flooredGrowth Q)
            (fun _ =>
              hierarchicalCommonGap
                (Fintype.card (OrderedPositiveSubface r))
                complexityBound Q ξ),
        (∀ j : Fin r,
          selectedGrowthCoarseComplexityBound
              k r initialBound (flooredGrowth Q) R.index j ≤
            complexityBound) →
        (∀ j : Fin r,
          R.selectedFineUpperComplexityBound j ≤
            complexityBound) →
        (∀ j : Fin r,
          R.selectedCoarseUpperComplexityBound j ≤
            complexityBound) →
        (∀ e : OrderedFace k r,
          OrderedPattern.faceDeletionDensity
              R.selectedCoarseBadBaseDeletionFamily e <
            ξ) ∧
        (∑ e : PositiveOrderedFace k r,
            (R.selectedDefectError e.rank +
              (R.selectedFineUpperComplexityBound
                  e.lowerRank : ℝ) *
                R.selectedRankTolerance e.lowerRank)) <
          ∏ e : PositiveOrderedFace k r,
            R.selectedDensityFloor e.rank := by
  obtain ⟨Q, hQ, hgapPos, hclean, _hgapCost, hcount⟩ :=
    exists_hierarchicalCommonScale_with_gap
      (Fintype.card (PositiveOrderedFace k r))
      (Fintype.card (OrderedPositiveSubface r))
      complexityBound hξ
  refine ⟨Q, hQ, hgapPos, ?_⟩
  intro R hcoarseWindow hfineUpperWindow
    hcoarseUpperWindow
  constructor
  · intro e
    exact
      R.faceDeletionDensity_selectedCoarseBadBase_lt_of_window
        hξ hcoarseWindow hfineUpperWindow
        hcoarseUpperWindow hQ hclean e
  · exact
      R.selectedCountingError_lt_densityProduct_of_window
        hcoarseWindow hfineUpperWindow
        (by omega) hcount

end Submission.GreenTao
