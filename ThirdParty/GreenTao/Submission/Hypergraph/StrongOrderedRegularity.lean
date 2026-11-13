import Submission.Hypergraph.OrderedEnergy
import Submission.Hypergraph.OrderedRegularizedCells

/-!
# Strong coarse--fine regularity for ordered patterns

Weak regularity may be iterated with tolerances fixed in advance from the
current *numeric* complexity bound.  The tower below keeps exact generator
certificates at every stage.  Bounded total energy then selects consecutive
coarse and fine stages with a small aggregate `L²` increment.

The selected gap is deliberately a fixed quantity.  A later cleaning layer
must charge cells unstable under this gap to an exceptional deletion rather
than attempting to force the gap below a complexity-dependent removal
modulus.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-- A fixed-budget generated regularization together with its initial
step-index bound. -/
structure GeneratedOrderedInitial
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) (H : WeightedOrderedPattern G k r)
    (ε : ℝ) (m : ℕ) where
  regularization :
    GeneratedOrderedPatternRegularization G k r H ε
  stepIndex_lt :
    ∀ e, regularization.stepIndex e < m

theorem GeneratedOrderedInitial.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ} {m : ℕ}
    (hr : 0 < r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    Nonempty (GeneratedOrderedInitial G k r H ε m) := by
  obtain ⟨R, hR⟩ :=
    exists_generatedOrderedPatternRegularization_before
      hr H hH hε hlong
  exact ⟨⟨R, hR⟩⟩

/-- One generated refinement step with its nesting and quantitative
step-index certificates. -/
structure GeneratedOrderedRefinement
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε : ℝ}
    (coarse :
      GeneratedOrderedPatternRegularization G k r H ε)
    (η : ℝ) (m : ℕ) where
  fine :
    GeneratedOrderedPatternRegularization G k r H η
  refines :
    OrderedRefines fine.state coarse.state
  generators_mono :
    ∀ e, coarse.generators e ⊆ fine.generators e
  stepIndex_lt :
    ∀ e, fine.stepIndex e < coarse.stepIndex e + m

theorem GeneratedOrderedRefinement.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε η : ℝ}
    (coarse :
      GeneratedOrderedPatternRegularization G k r H ε)
    (hr : 0 < r)
    (hH : H.EdgeWeightsInUnitInterval)
    {m : ℕ} (hη : 0 ≤ η)
    (hlong : 1 < (m : ℝ) * η ^ 2) :
    Nonempty
      (GeneratedOrderedRefinement coarse η m) := by
  obtain ⟨fine, hrefines, hgenerators, hstep⟩ :=
    coarse.exists_refinement_before
      hr hH hη hlong
  exact
    ⟨{
      fine := fine
      refines := hrefines
      generators_mono := hgenerators
      stepIndex_lt := hstep
    }⟩

/-- Canonical classical choice of the first tower stage. -/
noncomputable def chosenGeneratedOrderedInitial
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    {ε : ℝ} {m : ℕ}
    (hε : 0 ≤ ε)
    (hlong : 1 < (m : ℝ) * ε ^ 2) :
    GeneratedOrderedInitial G k r H ε m :=
  Classical.choice
    (GeneratedOrderedInitial.nonempty
      hr hH hε hlong)

/-- Canonical classical choice of one tower refinement. -/
noncomputable def chosenGeneratedOrderedRefinement
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε η : ℝ}
    (coarse :
      GeneratedOrderedPatternRegularization G k r H ε)
    (hr : 0 < r)
    (hH : H.EdgeWeightsInUnitInterval)
    {m : ℕ} (hη : 0 ≤ η)
    (hlong : 1 < (m : ℝ) * η ^ 2) :
    GeneratedOrderedRefinement coarse η m :=
  Classical.choice
    (GeneratedOrderedRefinement.nonempty
      coarse hr hH hη hlong)

/-- The generated strong-regularity tower for prescribed stage tolerances
and weak-regularity budgets. -/
noncomputable def generatedOrderedRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    (η : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ η n)
    (hlong :
      ∀ n, 1 < (budget n : ℝ) * (η n) ^ 2) :
    (n : ℕ) →
      GeneratedOrderedPatternRegularization
        G k r H (η n) :=
  Nat.rec
    (chosenGeneratedOrderedInitial
      H hH hr (hη 0) (hlong 0)).regularization
    (fun n coarse =>
      (chosenGeneratedOrderedRefinement
        coarse hr hH (hη (n + 1))
          (hlong (n + 1))).fine)

@[simp]
theorem generatedOrderedRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    (η : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ η n)
    (hlong :
      ∀ n, 1 < (budget n : ℝ) * (η n) ^ 2) :
    generatedOrderedRegularityTower
        H hH hr η budget hη hlong 0 =
      (chosenGeneratedOrderedInitial
        H hH hr (hη 0) (hlong 0)).regularization :=
  rfl

@[simp]
theorem generatedOrderedRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    (η : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ η n)
    (hlong :
      ∀ n, 1 < (budget n : ℝ) * (η n) ^ 2)
    (n : ℕ) :
    generatedOrderedRegularityTower
        H hH hr η budget hη hlong (n + 1) =
      (chosenGeneratedOrderedRefinement
        (generatedOrderedRegularityTower
          H hH hr η budget hη hlong n)
        hr hH (hη (n + 1))
          (hlong (n + 1))).fine :=
  rfl

/-- Every consecutive pair in the generated tower is nested. -/
theorem generatedOrderedRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    (η : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ η n)
    (hlong :
      ∀ n, 1 < (budget n : ℝ) * (η n) ^ 2)
    (n : ℕ) :
    OrderedRefines
      (generatedOrderedRegularityTower
        H hH hr η budget hη hlong (n + 1)).state
      (generatedOrderedRegularityTower
        H hH hr η budget hη hlong n).state := by
  rw [generatedOrderedRegularityTower_succ]
  exact
    (chosenGeneratedOrderedRefinement
      (generatedOrderedRegularityTower
        H hH hr η budget hη hlong n)
      hr hH (hη (n + 1))
        (hlong (n + 1))).refines

/-- Cumulative numeric bound on the generators adjoined through stage
`n`. -/
def cumulativeRegularityBudget
    (budget : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), budget j

@[simp]
theorem cumulativeRegularityBudget_zero
    (budget : ℕ → ℕ) :
    cumulativeRegularityBudget budget 0 = budget 0 := by
  simp [cumulativeRegularityBudget]

theorem cumulativeRegularityBudget_succ
    (budget : ℕ → ℕ) (n : ℕ) :
    cumulativeRegularityBudget budget (n + 1) =
      cumulativeRegularityBudget budget n +
        budget (n + 1) := by
  simp [cumulativeRegularityBudget,
    Finset.sum_range_succ, Nat.add_assoc]

/-- Every face step index is bounded by the precomputed cumulative budget,
independently of the ambient set and the pattern. -/
theorem generatedOrderedRegularityTower_stepIndex_lt
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    (η : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ η n)
    (hlong :
      ∀ n, 1 < (budget n : ℝ) * (η n) ^ 2) :
    ∀ n e,
      (generatedOrderedRegularityTower
        H hH hr η budget hη hlong n).stepIndex e <
      cumulativeRegularityBudget budget n := by
  intro n
  induction n with
  | zero =>
      intro e
      rw [generatedOrderedRegularityTower_zero,
        cumulativeRegularityBudget_zero]
      exact
        (chosenGeneratedOrderedInitial
          H hH hr (hη 0) (hlong 0)).stepIndex_lt e
  | succ n ih =>
      intro e
      rw [generatedOrderedRegularityTower_succ,
        cumulativeRegularityBudget_succ]
      have hnext :=
        (chosenGeneratedOrderedRefinement
          (generatedOrderedRegularityTower
            H hH hr η budget hη hlong n)
          hr hH (hη (n + 1))
            (hlong (n + 1))).stepIndex_lt e
      exact hnext.trans
        (Nat.add_lt_add_right (ih e) _)

/-- **Fixed-gap strong ordered regularity selector.**  Consecutive generated
coarse and fine systems can be selected so that their total energy gap is at
most the average energy budget.  Their generator bounds and the fine
regularity tolerance remain exactly those fixed by the input schedules. -/
theorem exists_generatedOrdered_coarse_fine_pair
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r)
    (η : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ η n)
    (hlong :
      ∀ n, 1 < (budget n : ℝ) * (η n) ^ 2)
    {m : ℕ} (hm : 0 < m) :
    ∃ i : ℕ, i < m ∧
      ∃ coarse :
          GeneratedOrderedPatternRegularization
            G k r H (η i),
      ∃ fine :
          GeneratedOrderedPatternRegularization
            G k r H (η (i + 1)),
        OrderedRefines fine.state coarse.state ∧
        orderedTotalEnergy H fine.state -
            orderedTotalEnergy H coarse.state ≤
          (Fintype.card (OrderedFace k r) : ℝ) /
            (m : ℝ) ∧
        (∀ e, coarse.stepIndex e <
          cumulativeRegularityBudget budget i) ∧
        (∀ e, fine.stepIndex e <
          cumulativeRegularityBudget budget (i + 1)) := by
  let tower :=
    generatedOrderedRegularityTower
      H hH hr η budget hη hlong
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_sub_le_div
      (fun n => orderedTotalEnergy H (tower n).state)
      hm
      (orderedTotalEnergy_nonneg H (tower 0).state)
      (orderedTotalEnergy_le_card hH (tower m).state)
  refine
    ⟨i, hi, tower i, tower (i + 1), ?_, hgap,
      ?_, ?_⟩
  · exact
      generatedOrderedRegularityTower_refines
        H hH hr η budget hη hlong i
  · exact
      generatedOrderedRegularityTower_stepIndex_lt
        H hH hr η budget hη hlong i
  · exact
      generatedOrderedRegularityTower_stepIndex_lt
        H hH hr η budget hη hlong (i + 1)

end Submission.GreenTao
