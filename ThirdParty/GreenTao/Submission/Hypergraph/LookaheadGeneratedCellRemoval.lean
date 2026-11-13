-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.GeneratedCellOrderedRemovalInduction
import Submission.Hypergraph.RankPrefixRemovalSelector

/-!
# Lookahead generated-cell removal

The direct generated-cell induction pays for one lower-rank deletion for
every cell of the regularization used in the count comparison.  If that is
the fine endpoint of a strong-regularity step, its complexity is known one
stage too late to choose the fine tolerance from the lower-rank removal
threshold.

There is an honest way to remove this particular shift.  Keep the generated
cells of the *coarse* endpoint, use the fine endpoint only to compare counts,
and invoke
`GeneratedOrderedPatternRegularization.lowerCellPattern_count_lt_of_fine_count`.
The recursive deletion loss is then the number of coarse cells.  The next
tolerance can be chosen after a bound for that coarse number is known.

This file packages that observation in a finite weighted lookahead
selector.  Its energy hypothesis is deliberately explicit: the sum of the
stage-dependent squared count margins must pay the complete ordered energy
budget.  Positivity of each margin alone does not imply this finite
cumulative inequality.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## An ambient-independent bound for the coarse cell count -/

/-- A common step-index bound gives this explicit bound for the number of
simultaneous atom/branch cells. -/
noncomputable def generatedCellIndexStepBound
    (k r stepBound : ℕ) : ℕ :=
  (2 ^ stepBound) ^
      Fintype.card (OrderedFace k r) *
    (r ^ stepBound) ^
      Fintype.card (OrderedFace k r)

/-- The cell count of a generated regularization is bounded by the common
step-index envelope. -/
theorem GeneratedOrderedPatternRegularization.card_cellIndex_le_stepBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {η : ℝ}
    (R : GeneratedOrderedPatternRegularization G k r H η)
    (hr : 0 < r) {stepBound : ℕ}
    (hstep : ∀ e, R.stepIndex e < stepBound) :
    Fintype.card R.CellIndex ≤
      generatedCellIndexStepBound k r stepBound := by
  apply (R.card_cellIndex_le hr).trans
  apply Nat.mul_le_mul
  · calc
      (∏ e : OrderedFace k r,
          2 ^ R.stepIndex e) ≤
          ∏ _e : OrderedFace k r,
            2 ^ stepBound := by
        apply Finset.prod_le_prod₀
        · intro e _he
          exact Nat.zero_le _
        · intro e _he
          exact Nat.pow_le_pow_right
            (by omega) (Nat.le_of_lt (hstep e))
      _ =
          (2 ^ stepBound) ^
            Fintype.card (OrderedFace k r) := by
        simp
  · calc
      (∏ e : OrderedFace k r,
          r ^ R.stepIndex e) ≤
          ∏ _e : OrderedFace k r,
            r ^ stepBound := by
        apply Finset.prod_le_prod₀
        · intro e _he
          exact Nat.zero_le _
        · intro e _he
          exact Nat.pow_le_pow_right
            hr (Nat.le_of_lt (hstep e))
      _ =
          (r ^ stepBound) ^
            Fintype.card (OrderedFace k r) := by
        simp

/-! ## Why a fixed-coarse block does not supply the stopping step -/

/-- Refining only the fine endpoint can only increase its energy gap above a
fixed coarse endpoint.  Thus an energy pigeonhole over a long block controls
adjacent increments, whose coarse endpoints move; it cannot be converted
into a new small fixed-coarse gap later in the block. -/
theorem orderedTotalEnergy_sub_fixedCoarse_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {fine₂ fine₁ coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine₂ fine₁) :
    orderedTotalEnergy H fine₁ -
        orderedTotalEnergy H coarse ≤
      orderedTotalEnergy H fine₂ -
        orderedTotalEnergy H coarse := by
  exact sub_le_sub_right
    (orderedTotalEnergy_mono H hrefines) _

/-! ## Lower-rank thresholds can be chosen stage by stage -/

/-- Ordinary lower-rank removal supplies a positive threshold for every
precomputed positive recursive cost.  Hence choosing the stagewise
thresholds is not the obstruction in the lookahead construction. -/
theorem exists_lookaheadRecursiveThresholds_of_uniformRemoval
    {k r : ℕ}
    (hlower : HasUniformOrderedPatternRemoval k (r - 1))
    (recursiveCost : ℕ → ℝ)
    (hcost : ∀ i, 0 < recursiveCost i) :
    ∃ recursiveThreshold : ℕ → ℝ,
      (∀ i, 0 < recursiveThreshold i) ∧
      ∀ i,
        ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
          ∀ L : OrderedPattern G k (r - 1),
            L.toWeighted.patternCount <
                recursiveThreshold i →
              ∃ D : OrderedPattern.DeletionFamily
                  (G := G) k (r - 1),
                L.IsCover D ∧
                  ∀ g,
                    OrderedPattern.faceDeletionDensity D g ≤
                      recursiveCost i := by
  have hchoice :
      ∀ i,
        ∃ c : ℝ, 0 < c ∧
          ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
            ∀ L : OrderedPattern G k (r - 1),
              L.toWeighted.patternCount < c →
                ∃ D : OrderedPattern.DeletionFamily
                    (G := G) k (r - 1),
                  L.IsCover D ∧
                    ∀ g,
                      OrderedPattern.faceDeletionDensity D g ≤
                        recursiveCost i :=
    fun i => hlower (recursiveCost i) (hcost i)
  choose recursiveThreshold hthreshold using hchoice
  exact
    ⟨recursiveThreshold,
      fun i => (hthreshold i).1,
      fun i => (hthreshold i).2⟩

/-! ## The finite lookahead schedule -/

/-- Numerical and lower-rank removal data along one finite generated
regularity tower.

At stage `i`, `recursiveThreshold i` and `recursiveCost i` are chosen using
the known bound for the *coarse* endpoint.  The tolerance at `i + 1` then
makes the fine structured count small enough for that threshold.

The last field is the sharp remaining stopping condition.  The factor two
leaves strict room in the square-gap estimate consumed by the coarse-cell
count bridge. -/
structure LookaheadGeneratedCellRemovalSchedule
    (k r : ℕ) (ε : ℝ) where
  length : ℕ
  length_pos : 0 < length
  densityFloor : ℝ
  densityFloor_pos : 0 < densityFloor
  tolerance : ℕ → ℝ
  budget : ℕ → ℕ
  tolerance_nonneg : ∀ n, 0 ≤ tolerance n
  budget_long :
    ∀ n,
      1 < (budget n : ℝ) * (tolerance n) ^ 2
  gapMargin : ℕ → ℝ
  gapMargin_pos :
    ∀ i, i < length → 0 < gapMargin i
  recursiveCost : ℕ → ℝ
  recursiveCost_pos :
    ∀ i, i < length → 0 < recursiveCost i
  recursiveThreshold : ℕ → ℝ
  recursiveThreshold_pos :
    ∀ i, i < length → 0 < recursiveThreshold i
  recursiveRemoval :
    ∀ i, i < length →
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ L : OrderedPattern G k (r - 1),
          L.toWeighted.patternCount < recursiveThreshold i →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k (r - 1),
              L.IsCover D ∧
                ∀ g,
                  OrderedPattern.faceDeletionDensity D g ≤
                    recursiveCost i
  topCountThreshold : ℝ
  topCountThreshold_pos : 0 < topCountThreshold
  count_lookahead :
    ∀ i, i < length →
      topCountThreshold +
          (Fintype.card (OrderedFace k r) : ℝ) *
            tolerance (i + 1) +
          gapMargin i <
        densityFloor ^
            Fintype.card (OrderedFace k r) *
          recursiveThreshold i
  deletion_budget :
    ∀ i, i < length →
      densityFloor +
          (generatedCellIndexStepBound k r
              (cumulativeRegularityBudget budget i) : ℝ) *
            (r : ℝ) * recursiveCost i ≤
        ε
  cumulative_gap_budget :
    (Fintype.card (OrderedFace k r) : ℝ) ≤
      ∑ i ∈ Finset.range length,
        gapMargin i ^ 2 /
          (2 * (Fintype.card (OrderedFace k r) : ℝ))

/-! ## Coarse-cell weighted stopping -/

/-- A finite lookahead schedule gives uniform rank-`r` removal.

Only the selected adjacent pair is used.  The coarse endpoint supplies the
generated lower cells and hence the recursive multiplicity; the fine
endpoint supplies the count comparison. -/
theorem
    LookaheadGeneratedCellRemovalSchedule.hasUniformOrderedPatternRemoval
    {k r : ℕ} {ε : ℝ}
    (S : LookaheadGeneratedCellRemovalSchedule k r ε)
    (hr : 0 < r) (hrk : r ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e,
                  OrderedPattern.faceDeletionDensity D e ≤ ε := by
  refine
    ⟨S.topCountThreshold, S.topCountThreshold_pos, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  let tower :=
    generatedOrderedRegularityTower
      H.toWeighted H.toWeighted_unitInterval hr
      S.tolerance S.budget
      S.tolerance_nonneg S.budget_long
  let energy : ℕ → ℝ :=
    fun n => orderedTotalEnergy H.toWeighted (tower n).state
  let weight : ℕ → ℝ :=
    fun i =>
      S.gapMargin i ^ 2 /
        (2 * (Fintype.card (OrderedFace k r) : ℝ))
  have hfaceNat :
      0 < Fintype.card (OrderedFace k r) :=
    card_orderedFace_pos_of_le hrk
  have hface :
      (0 : ℝ) <
        Fintype.card (OrderedFace k r) := by
    exact_mod_cast hfaceNat
  have hweight :
      ∀ i, i < S.length → 0 < weight i := by
    intro i hi
    dsimp [weight]
    exact div_pos (sq_pos_of_pos (S.gapMargin_pos i hi))
      (mul_pos (by norm_num) hface)
  have henergyBudget :
      (Fintype.card (OrderedFace k r) : ℝ) ≤
        ∑ i ∈ Finset.range S.length, 1 * weight i := by
    simpa only [one_mul, weight] using
      S.cumulative_gap_budget
  obtain ⟨i, hi, hselected⟩ :=
    exists_adjacent_real_sub_div_le_of_weighted_budget
      energy weight S.length_pos
      (B := (Fintype.card (OrderedFace k r) : ℝ))
      (ξ := 1)
      (orderedTotalEnergy_nonneg
        H.toWeighted (tower 0).state)
      (orderedTotalEnergy_le_card
        H.toWeighted_unitInterval (tower S.length).state)
      hweight henergyBudget
  let coarse := tower i
  let fine := tower (i + 1)
  have hrefines :
      OrderedRefines fine.state coarse.state := by
    exact
      generatedOrderedRegularityTower_refines
        H.toWeighted H.toWeighted_unitInterval hr
        S.tolerance S.budget
        S.tolerance_nonneg S.budget_long i
  have hgapLe :
      orderedTotalEnergy H.toWeighted fine.state -
          orderedTotalEnergy H.toWeighted coarse.state ≤
        weight i := by
    have h :=
      (div_le_iff₀ (hweight i hi)).1 hselected
    simpa only [energy, coarse, fine, one_mul] using h
  have hgap :
      (Fintype.card (OrderedFace k r) : ℝ) *
          (orderedTotalEnergy H.toWeighted fine.state -
            orderedTotalEnergy H.toWeighted coarse.state) <
        S.gapMargin i ^ 2 := by
    have hhalf :
        (Fintype.card (OrderedFace k r) : ℝ) *
            (orderedTotalEnergy H.toWeighted fine.state -
              orderedTotalEnergy H.toWeighted coarse.state) ≤
          S.gapMargin i ^ 2 / 2 := by
      calc
        (Fintype.card (OrderedFace k r) : ℝ) *
              (orderedTotalEnergy H.toWeighted fine.state -
                orderedTotalEnergy H.toWeighted coarse.state) ≤
            (Fintype.card (OrderedFace k r) : ℝ) *
              weight i :=
          mul_le_mul_of_nonneg_left hgapLe hface.le
        _ = S.gapMargin i ^ 2 / 2 := by
          dsimp [weight]
          field_simp
    nlinarith [sq_pos_of_pos (S.gapMargin_pos i hi)]
  have hfineCountUpper :
      (regularizedOrderedPattern
          H.toWeighted fine.state).patternCount ≤
        H.toWeighted.patternCount +
          (Fintype.card (OrderedFace k r) : ℝ) *
            S.tolerance (i + 1) := by
    have hdiff :
        (regularizedOrderedPattern
            H.toWeighted fine.state).patternCount -
            H.toWeighted.patternCount ≤
          |H.toWeighted.patternCount -
            (regularizedOrderedPattern
              H.toWeighted fine.state).patternCount| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have hclose := fine.count_close
    linarith
  have hfineSmall :
      (regularizedOrderedPattern
          H.toWeighted fine.state).patternCount +
          S.gapMargin i <
        S.densityFloor ^
            Fintype.card (OrderedFace k r) *
          S.recursiveThreshold i := by
    have hupper :
        (regularizedOrderedPattern
            H.toWeighted fine.state).patternCount +
            S.gapMargin i ≤
          H.toWeighted.patternCount +
              (Fintype.card (OrderedFace k r) : ℝ) *
                S.tolerance (i + 1) +
            S.gapMargin i :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hfineCountUpper (S.gapMargin i)
    exact hupper.trans_lt
      (lt_of_lt_of_le
        (by
          linarith [hcount])
        (S.count_lookahead i hi).le)
  have hcellSmall :
      ∀ a : coarse.TopAtomChoice,
        coarse.IsHeavy S.densityFloor a →
          ∀ w : coarse.BranchSystem,
            (coarse.lowerCellPattern a w).toWeighted.patternCount <
              S.recursiveThreshold i := by
    intro a ha w
    exact
      coarse.lowerCellPattern_count_lt_of_fine_count
        fine.state hrefines H.toWeighted_unitInterval
        hr S.densityFloor_pos
        (S.gapMargin_pos i hi) hgap hfineSmall a ha w
  obtain ⟨D, hcover, hdensity⟩ :=
    coarse.exists_generatedCellCover_of_lowerCellCounts
      H hr hrk S.densityFloor_pos
      (S.recursiveCost_pos i hi).le
      hcellSmall
      (S.recursiveRemoval i hi G)
  refine ⟨D, hcover, ?_⟩
  intro e
  have hstep :
      ∀ f,
        coarse.stepIndex f <
          cumulativeRegularityBudget S.budget i := by
    exact
      generatedOrderedRegularityTower_stepIndex_lt
        H.toWeighted H.toWeighted_unitInterval hr
        S.tolerance S.budget
        S.tolerance_nonneg S.budget_long i
  have hcardNat :
      Fintype.card coarse.CellIndex ≤
        generatedCellIndexStepBound k r
          (cumulativeRegularityBudget S.budget i) :=
    coarse.card_cellIndex_le_stepBound hr hstep
  have hcard :
      (Fintype.card coarse.CellIndex : ℝ) ≤
        generatedCellIndexStepBound k r
          (cumulativeRegularityBudget S.budget i) := by
    exact_mod_cast hcardNat
  have hrecursive :
      (Fintype.card coarse.CellIndex : ℝ) *
          (r : ℝ) * S.recursiveCost i ≤
        (generatedCellIndexStepBound k r
            (cumulativeRegularityBudget S.budget i) : ℝ) *
          (r : ℝ) * S.recursiveCost i := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right hcard (by positivity)
    · exact (S.recursiveCost_pos i hi).le
  calc
    OrderedPattern.faceDeletionDensity D e ≤
        S.densityFloor +
          (Fintype.card coarse.CellIndex : ℝ) *
            (r : ℝ) * S.recursiveCost i :=
      hdensity e
    _ ≤
        S.densityFloor +
          (generatedCellIndexStepBound k r
              (cumulativeRegularityBudget S.budget i) : ℝ) *
            (r : ℝ) * S.recursiveCost i := by
      linarith
    _ ≤ ε :=
      S.deletion_budget i hi

/-- Existence of a lookahead schedule at every positive target cost is the
precise factored hypothesis needed for a rank step. -/
def HasLookaheadGeneratedCellRemovalSchedules
    (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Nonempty (LookaheadGeneratedCellRemovalSchedule k r ε)

/-- The factored schedule hypothesis implies uniform ordered removal. -/
theorem hasUniformOrderedPatternRemoval_of_lookaheadGeneratedCellSchedules
    {k r : ℕ}
    (hr : 0 < r) (hrk : r ≤ k)
    (hschedule :
      HasLookaheadGeneratedCellRemovalSchedules k r) :
    HasUniformOrderedPatternRemoval k r := by
  intro ε hε
  obtain ⟨S⟩ := hschedule ε hε
  exact S.hasUniformOrderedPatternRemoval hr hrk

end Submission.GreenTao
