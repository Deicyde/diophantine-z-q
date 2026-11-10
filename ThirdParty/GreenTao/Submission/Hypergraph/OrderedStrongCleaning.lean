-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.OrderedCellLifting
import Submission.Hypergraph.StrongOrderedRegularity

/-!
# Cleaning a coarse--fine ordered regularity pair

The small `L²` component of a strong regularity pair is charged to explicit
top-face deletions.  This file proves the finite Chebyshev estimate and the
pointwise fact that, outside those deletions, a coarse-heavy cell remains
heavy for the fine structured pattern.

This is intentionally only the fixed-gap cleaning layer.  Recursive removal
on stable cells is kept separate from the exceptional-cell bookkeeping.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-- Face tuples on which the fine and coarse structured densities differ by
more than `θ`. -/
noncomputable def structuredDeviationDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (fine coarse : OrderedRegularitySystem G k r)
    (θ : ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e =>
    Finset.univ.filter fun y =>
      θ <
        |(fine e).structured (H.edgeWeight e) y -
          (coarse e).structured (H.edgeWeight e) y|

@[simp]
theorem mem_structuredDeviationDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (fine coarse : OrderedRegularitySystem G k r)
    (θ : ℝ) (e : OrderedFace k r)
    (y : Fin r → G) :
    y ∈ structuredDeviationDeletion H fine coarse θ e ↔
      θ <
        |(fine e).structured (H.edgeWeight e) y -
          (coarse e).structured (H.edgeWeight e) y| := by
  simp [structuredDeviationDeletion]

/-- Finite normalized Chebyshev inequality, in multiplication form so that
no division or positivity side condition is needed. -/
theorem sq_mul_mean_indicator_deviation_le_mean_sq
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (d : Ω → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    θ ^ 2 *
        mean (finsetIndicator
          (Finset.univ.filter fun x => θ < |d x|)) ≤
      mean (fun x => d x ^ 2) := by
  rw [← mean_smul]
  apply mean_mono
  intro x
  by_cases hx : θ < |d x|
  · rw [finsetIndicator_of_mem]
    · simpa only [mul_one, sq_abs] using
        (sq_le_sq₀ hθ (abs_nonneg (d x))).2 hx.le
    · simp [hx]
  · rw [finsetIndicator_of_not_mem, mul_zero]
    · exact sq_nonneg (d x)
    · simp [hx]

/-- The density of one deviation deletion is its normalized indicator
mean. -/
theorem faceDeletionDensity_structuredDeviationDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (fine coarse : OrderedRegularitySystem G k r)
    (θ : ℝ) (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (structuredDeviationDeletion H fine coarse θ) e =
      mean (finsetIndicator
        (structuredDeviationDeletion H fine coarse θ e)) := by
  rw [mean_finsetIndicator]
  rfl

/-- A single face's mean-square structured discrepancy is bounded by the
total ordered energy increment. -/
theorem face_mean_sq_le_orderedTotalEnergy_sub
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse)
    (e : OrderedFace k r) :
    mean (fun y =>
        ((fine e).structured (H.edgeWeight e) y -
          (coarse e).structured (H.edgeWeight e) y) ^ 2) ≤
      orderedTotalEnergy H fine -
        orderedTotalEnergy H coarse := by
  rw [orderedTotalEnergy_sub_eq_sum_mean_sq H hrefines]
  change
    mean (fun y =>
        ((fine e).structured (H.edgeWeight e) y -
          (coarse e).structured (H.edgeWeight e) y) ^ 2) ≤
      ∑ f ∈ (Finset.univ : Finset (OrderedFace k r)),
        mean (fun y =>
          ((fine f).structured (H.edgeWeight f) y -
            (coarse f).structured (H.edgeWeight f) y) ^ 2)
  exact
    Finset.single_le_sum
      (s := (Finset.univ : Finset (OrderedFace k r)))
      (f := fun f =>
        mean (fun y =>
          ((fine f).structured (H.edgeWeight f) y -
            (coarse f).structured (H.edgeWeight f) y) ^ 2))
      (fun f _hf => mean_nonneg fun y => sq_nonneg _)
      (Finset.mem_univ e)

/-- Chebyshev bound for the exceptional top-face deletion, charged directly
to the total coarse--fine energy gap. -/
theorem sq_mul_faceDeletionDensity_structuredDeviationDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (e : OrderedFace k r) :
    θ ^ 2 *
        OrderedPattern.faceDeletionDensity
          (structuredDeviationDeletion
            H fine coarse θ) e ≤
      orderedTotalEnergy H fine -
        orderedTotalEnergy H coarse := by
  rw [faceDeletionDensity_structuredDeviationDeletion]
  exact
    (sq_mul_mean_indicator_deviation_le_mean_sq
      (fun y =>
        (fine e).structured (H.edgeWeight e) y -
          (coarse e).structured (H.edgeWeight e) y)
      hθ).trans
      (face_mean_sq_le_orderedTotalEnergy_sub
        H hrefines e)

/-- Divided form of the exceptional-deletion estimate. -/
theorem faceDeletionDensity_structuredDeviationDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse)
    {θ ξ : ℝ} (hθ : 0 < θ)
    (hgap :
      orderedTotalEnergy H fine -
          orderedTotalEnergy H coarse ≤
        θ ^ 2 * ξ)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (structuredDeviationDeletion
          H fine coarse θ) e ≤ ξ := by
  have hmul :
      θ ^ 2 *
          OrderedPattern.faceDeletionDensity
            (structuredDeviationDeletion
              H fine coarse θ) e ≤
        θ ^ 2 * ξ :=
    (sq_mul_faceDeletionDensity_structuredDeviationDeletion_le
      H hrefines hθ.le e).trans hgap
  nlinarith [sq_pos_of_pos hθ]

/-- Outside the exceptional deletion, fine and coarse structured densities
differ by at most `θ`. -/
theorem abs_structured_sub_le_of_not_mem_deviation
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (fine coarse : OrderedRegularitySystem G k r)
    {θ : ℝ} (e : OrderedFace k r)
    (y : Fin r → G)
    (hy :
      y ∉ structuredDeviationDeletion
        H fine coarse θ e) :
    |(fine e).structured (H.edgeWeight e) y -
        (coarse e).structured (H.edgeWeight e) y| ≤ θ := by
  exact not_lt.mp
    (fun h => hy
      ((mem_structuredDeviationDeletion
        H fine coarse θ e y).2 h))

namespace GeneratedOrderedPatternRegularization

/-- On a coarse-heavy atom, avoidance of the deviation deletion gives the
pointwise fine lower bound `τ - θ`. -/
theorem sub_le_fine_structured_of_heavy_of_not_mem_deviation
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ θ : ℝ}
    (coarse :
      GeneratedOrderedPatternRegularization
        G k r H ε)
    (fine : OrderedRegularitySystem G k r)
    (a : coarse.TopAtomChoice)
    (ha : coarse.IsHeavy τ a)
    (e : OrderedFace k r)
    (x : Fin k → G)
    (hmem :
      orderedFaceTuple e x ∈ (a e).1)
    (havoid :
      orderedFaceTuple e x ∉
        structuredDeviationDeletion
          H fine coarse.state θ e) :
    τ - θ ≤
      (fine e).structured (H.edgeWeight e)
        (orderedFaceTuple e x) := by
  have hcoarse :
      (coarse.state e).structured (H.edgeWeight e)
          (orderedFaceTuple e x) =
        coarse.atomEdgeWeight a e := by
    exact
      coarse.regularized_edgeWeight_eq_atomEdgeWeight
        a e x hmem
  have hdiff :=
    abs_structured_sub_le_of_not_mem_deviation
      H fine coarse.state e
        (orderedFaceTuple e x) havoid
  have hlower := (abs_le.mp hdiff).1
  have hheavy := ha e
  rw [hcoarse] at hlower
  linarith

/-- A lower-cell occurrence which avoids every deviation face has fine
structured pattern weight at least `(τ - θ)^q`. -/
theorem sub_pow_le_fine_patternWeight_of_lowerCellOccurrence
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ θ : ℝ}
    (coarse :
      GeneratedOrderedPatternRegularization
        G k r H ε)
    (fine : OrderedRegularitySystem G k r)
    (hr : 0 < r)
    (hsub : 0 ≤ τ - θ)
    (a : coarse.TopAtomChoice)
    (ha : coarse.IsHeavy τ a)
    (w : coarse.BranchSystem)
    {x : Fin k → G}
    (hx :
      (coarse.lowerCellPattern a w).IsOccurrence x)
    (havoid :
      ∀ e,
        orderedFaceTuple e x ∉
          structuredDeviationDeletion
            H fine coarse.state θ e) :
    (τ - θ) ^ Fintype.card (OrderedFace k r) ≤
      (regularizedOrderedPattern H fine).patternWeight x := by
  have hcell :
      coarse.IsInAtomBranch a w x :=
    (coarse.lowerCellPattern_isOccurrence_iff
      a w x).1 hx
  have hmem :
      ∀ e, orderedFaceTuple e x ∈ (a e).1 :=
    (coarse.mem_all_topAtoms_iff_exists_branchSystem
      hr a x).2 ⟨w, hcell⟩
  unfold WeightedOrderedPattern.patternWeight
  have hprod :
      (∏ _e ∈ (Finset.univ :
          Finset (OrderedFace k r)), (τ - θ)) ≤
        ∏ e ∈ (Finset.univ :
            Finset (OrderedFace k r)),
          (fine e).structured (H.edgeWeight e)
            (orderedFaceTuple e x) := by
    apply Finset.prod_le_prod₀
    · intro e _he
      exact hsub
    · intro e _he
      exact
        coarse.sub_le_fine_structured_of_heavy_of_not_mem_deviation
          fine a ha e x (hmem e) (havoid e)
  simpa using hprod

/-- A conditional all-cell bridge from a sufficiently small fine structured
count and a sufficiently tiny coarse--fine energy gap.  The strong removal
proof cannot use this with a complexity-dependent `γ` directly, but the
lemma is useful whenever such a uniform square-gap estimate is available. -/
theorem lowerCellPattern_count_lt_of_fine_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {ε τ γ cLower : ℝ}
    (coarse :
      GeneratedOrderedPatternRegularization
        G k r H ε)
    (fine : OrderedRegularitySystem G k r)
    (hrefines : OrderedRefines fine coarse.state)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r) (hτ : 0 < τ)
    (hγ : 0 < γ)
    (hgap :
      (Fintype.card (OrderedFace k r) : ℝ) *
          (orderedTotalEnergy H fine -
            orderedTotalEnergy H coarse.state) <
        γ ^ 2)
    (hsmall :
      (regularizedOrderedPattern H fine).patternCount + γ <
        τ ^ Fintype.card (OrderedFace k r) * cLower)
    (a : coarse.TopAtomChoice)
    (ha : coarse.IsHeavy τ a)
    (w : coarse.BranchSystem) :
    (coarse.lowerCellPattern a w).toWeighted.patternCount <
      cLower := by
  have hclose :=
    regularizedOrderedPattern_count_abs_sub_lt_of_energyGap
      hH hrefines hγ hgap
  have hcoarse :
      (regularizedOrderedPattern
          H coarse.state).patternCount <
        (regularizedOrderedPattern H fine).patternCount +
          γ := by
    have hdiff :
        (regularizedOrderedPattern H coarse.state).patternCount -
            (regularizedOrderedPattern H fine).patternCount ≤
          |(regularizedOrderedPattern H fine).patternCount -
            (regularizedOrderedPattern H coarse.state).patternCount| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  exact
    coarse.lowerCellPattern_count_lt_of_regularized_count_lt
      hH hr hτ a ha w (hcoarse.trans hsmall)

end GeneratedOrderedPatternRegularization

end Submission.GreenTao
