import Submission.Hypergraph.OrderedStrongCleaning

/-!
# Generated-cell ordered removal induction

This file isolates the strongest non-circular semantic induction statement
available from the generated-cell regularity API.

The first key point is exact: a coarse--fine structured deviation predicate
is constant on every fine atom.  Consequently a generated fine cell is
either stable on every top face, or every occurrence of that cell meets the
explicit deviation deletion.  This supplies the exact active/inactive cover
interface required by `exists_generatedCellCover_of_activeLowerCellCounts`.

The resulting induction step is fully formal, but its recursive deletion
cost is multiplied by the number of *fine* cells.  The fixed coarse--fine
energy gap does not bound that number at the preceding coarse stage.  Thus
ordinary lower-rank removal, whose count threshold may depend arbitrarily on
the requested deletion cost, does not by itself instantiate the theorem.

For comparison, the last section proves that generated-cell induction does
close if the lower rank has one positive count threshold valid uniformly for
all deletion costs.  Rank zero has exactly this stronger property, giving an
independent generated-cell proof of rank-one removal.  The property is not
supplied by ordinary removal at positive rank, which pinpoints the remaining
quantifier obstruction.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Deviation predicates are constant on fine atoms -/

/-- A structured deviation predicate is constant on atoms of the fine
partition.  Refinement is needed for the coarse structured component. -/
theorem mem_structuredDeviationDeletion_iff_of_mem_fine_part
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (fine coarse : OrderedRegularitySystem G k r)
    (hrefines : OrderedRefines fine coarse)
    (θ : ℝ) (e : OrderedFace k r)
    {x y : Fin r → G}
    (hy : y ∈ (fine e).partition.part x) :
    y ∈ structuredDeviationDeletion H fine coarse θ e ↔
      x ∈ structuredDeviationDeletion H fine coarse θ e := by
  have hfine :
      (fine e).structured (H.edgeWeight e) y =
        (fine e).structured (H.edgeWeight e) x := by
    exact
      conditionalMean_eq_of_mem_part
        (fine e).partition (H.edgeWeight e) hy
  have hcoarseMem :
      y ∈ (coarse e).partition.part x :=
    FacePartition.part_subset_of_le (hrefines e) x hy
  have hcoarse :
      (coarse e).structured (H.edgeWeight e) y =
        (coarse e).structured (H.edgeWeight e) x := by
    exact
      conditionalMean_eq_of_mem_part
        (coarse e).partition (H.edgeWeight e) hcoarseMem
  rw [mem_structuredDeviationDeletion,
    mem_structuredDeviationDeletion, hfine, hcoarse]

namespace GeneratedOrderedPatternRegularization

/-- A fine generated cell is stable when the representative of each of its
selected fine top atoms avoids the coarse--fine deviation deletion. -/
def IsDeviationStable
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {η : ℝ}
    (fine :
      GeneratedOrderedPatternRegularization G k r H η)
    (coarse : OrderedRegularitySystem G k r)
    (θ : ℝ) (p : fine.CellIndex) : Prop :=
  ∀ e,
    (fine.state e).partition.representative (p.1 e) ∉
      structuredDeviationDeletion
        H fine.state coarse θ e

/-- Every occurrence of a stable fine cell avoids the deviation deletion on
every top face. -/
theorem avoids_structuredDeviationDeletion_of_isDeviationStable
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {η : ℝ}
    (fine :
      GeneratedOrderedPatternRegularization G k r H η)
    (coarse : OrderedRegularitySystem G k r)
    (hrefines : OrderedRefines fine.state coarse)
    (hr : 0 < r) (θ : ℝ)
    (p : fine.CellIndex)
    (hstable : fine.IsDeviationStable coarse θ p)
    {x : Fin k → G}
    (hx : (fine.lowerCellPattern p.1 p.2).IsOccurrence x) :
    ∀ e,
      orderedFaceTuple e x ∉
        structuredDeviationDeletion
          H fine.state coarse θ e := by
  have hcell : fine.IsInAtomBranch p.1 p.2 x :=
    (fine.lowerCellPattern_isOccurrence_iff p.1 p.2 x).1 hx
  have hmem :
      ∀ e, orderedFaceTuple e x ∈ (p.1 e).1 :=
    (fine.mem_all_topAtoms_iff_exists_branchSystem
      hr p.1 x).2 ⟨p.2, hcell⟩
  intro e hbad
  have hpart :
      orderedFaceTuple e x ∈
        (fine.state e).partition.part
          ((fine.state e).partition.representative
            (p.1 e)) := by
    rw [(fine.state e).partition.part_representative]
    exact hmem e
  have hiff :=
    mem_structuredDeviationDeletion_iff_of_mem_fine_part
      H fine.state coarse hrefines θ e hpart
  exact hstable e (hiff.mp hbad)

/-- Conversely, every occurrence of an unstable fine cell meets the
deviation deletion.  This is the exact saturation statement which fails
for mixed coarse cells but holds for genuine fine atoms. -/
theorem exists_mem_structuredDeviationDeletion_of_not_isDeviationStable
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {η : ℝ}
    (fine :
      GeneratedOrderedPatternRegularization G k r H η)
    (coarse : OrderedRegularitySystem G k r)
    (hrefines : OrderedRefines fine.state coarse)
    (hr : 0 < r) (θ : ℝ)
    (p : fine.CellIndex)
    {x : Fin k → G}
    (hx : (fine.lowerCellPattern p.1 p.2).IsOccurrence x)
    (hunstable : ¬fine.IsDeviationStable coarse θ p) :
    ∃ e,
      orderedFaceTuple e x ∈
        structuredDeviationDeletion
          H fine.state coarse θ e := by
  have hcell : fine.IsInAtomBranch p.1 p.2 x :=
    (fine.lowerCellPattern_isOccurrence_iff p.1 p.2 x).1 hx
  have hmem :
      ∀ e, orderedFaceTuple e x ∈ (p.1 e).1 :=
    (fine.mem_all_topAtoms_iff_exists_branchSystem
      hr p.1 x).2 ⟨p.2, hcell⟩
  simp only [IsDeviationStable, not_forall] at hunstable
  obtain ⟨e, hbadRepresentative⟩ := hunstable
  push Not at hbadRepresentative
  refine ⟨e, ?_⟩
  have hpart :
      orderedFaceTuple e x ∈
        (fine.state e).partition.part
          ((fine.state e).partition.representative
            (p.1 e)) := by
    rw [(fine.state e).partition.part_representative]
    exact hmem e
  exact
    (mem_structuredDeviationDeletion_iff_of_mem_fine_part
      H fine.state coarse hrefines θ e hpart).2
      hbadRepresentative

/-! ## The exact semantic coarse--fine induction step -/

/-- Generated fine cells turn a fixed-gap coarse--fine pair into a valid
active/inactive recursive removal step.

Stable fine cells are sent to lower-rank removal.  Unstable fine cells are
covered exactly by the deviation deletion, whose density is controlled by
the coarse--fine energy gap.  The unavoidable recursive multiplicity is the
number of fine cell indices. -/
theorem exists_generatedFineCellCover_of_coarseFinePair
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    {η σ θ δ ξ cLower : ℝ}
    (fine :
      GeneratedOrderedPatternRegularization
        G k r H.toWeighted η)
    (coarse : OrderedRegularitySystem G k r)
    (hrefines : OrderedRefines fine.state coarse)
    (hr : 0 < r) (hrk : r ≤ k)
    (hσ : 0 < σ) (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hgap :
      orderedTotalEnergy H.toWeighted fine.state -
          orderedTotalEnergy H.toWeighted coarse ≤
        θ ^ 2 * ξ)
    (hsmall :
      (regularizedOrderedPattern
          H.toWeighted fine.state).patternCount <
        σ ^ Fintype.card (OrderedFace k r) * cLower)
    (hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k r,
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤
            σ +
              (Fintype.card fine.CellIndex : ℝ) *
                (r : ℝ) * δ +
              ξ := by
  apply
    fine.exists_generatedCellCover_of_activeLowerCellCounts
      H hr hrk hσ hδ
      (fine.IsDeviationStable coarse θ)
      (structuredDeviationDeletion
        H.toWeighted fine.state coarse θ)
  · intro e
    exact
      faceDeletionDensity_structuredDeviationDeletion_le
        H.toWeighted hrefines hθ hgap e
  · intro a w x _ha hx hunstable
    exact
      fine.exists_mem_structuredDeviationDeletion_of_not_isDeviationStable
        coarse hrefines hr θ (a, w) hx hunstable
  · intro a ha w _hstable
    exact
      fine.lowerCellPattern_count_lt_of_regularized_count_lt
        H.toWeighted_unitInterval hr hσ
        a ha w hsmall
  · exact hremove

/-- Original-pattern count form of the semantic coarse--fine induction
step.  The fine regularization's weak counting error is exposed explicitly,
rather than hidden behind a non-uniform parameter choice. -/
theorem exists_generatedFineCellCover_of_coarseFinePair_of_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    {η σ θ δ ξ cLower : ℝ}
    (fine :
      GeneratedOrderedPatternRegularization
        G k r H.toWeighted η)
    (coarse : OrderedRegularitySystem G k r)
    (hrefines : OrderedRefines fine.state coarse)
    (hr : 0 < r) (hrk : r ≤ k)
    (hσ : 0 < σ) (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hgap :
      orderedTotalEnergy H.toWeighted fine.state -
          orderedTotalEnergy H.toWeighted coarse ≤
        θ ^ 2 * ξ)
    (hcount :
      H.toWeighted.patternCount +
          (Fintype.card (OrderedFace k r) : ℝ) * η <
        σ ^ Fintype.card (OrderedFace k r) * cLower)
    (hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k r,
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤
            σ +
              (Fintype.card fine.CellIndex : ℝ) *
                (r : ℝ) * δ +
              ξ := by
  apply
    fine.exists_generatedFineCellCover_of_coarseFinePair
      H coarse hrefines hr hrk hσ hθ hδ hgap
  · have hdiff :
        (regularizedOrderedPattern
            H.toWeighted fine.state).patternCount -
            H.toWeighted.patternCount ≤
          |H.toWeighted.patternCount -
            (regularizedOrderedPattern
              H.toWeighted fine.state).patternCount| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    exact
      lt_of_le_of_lt
        (by linarith [fine.count_close])
        hcount
  · exact hremove

/-- Direct corollary of the fixed-gap strong regularity selector.

The selected fine cell system has an explicit deviation cost

`card (OrderedFace k r) / (m * θ²)`.

For that selected pair, any independently supplied fine-count margin gives
the recursive cover.  Notice that the recursive multiplicity in the
conclusion is still `fine.CellIndex`, not the preceding coarse cell count.
This is the exact one-stage shift responsible for the uniform-parameter
obstruction at positive lower rank. -/
theorem exists_fixedGapGeneratedFineCellCoverImplication
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (hr : 0 < r) (hrk : r ≤ k)
    (ηSchedule : ℕ → ℝ) (budget : ℕ → ℕ)
    (hη : ∀ n, 0 ≤ ηSchedule n)
    (hlong :
      ∀ n,
        1 < (budget n : ℝ) * (ηSchedule n) ^ 2)
    {m : ℕ} (hm : 0 < m)
    {σ θ δ cLower : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (hδ : 0 ≤ δ)
    (hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ) :
    ∃ i : ℕ, i < m ∧
      ∃ coarse :
          GeneratedOrderedPatternRegularization
            G k r H.toWeighted (ηSchedule i),
      ∃ fine :
          GeneratedOrderedPatternRegularization
            G k r H.toWeighted (ηSchedule (i + 1)),
        OrderedRefines fine.state coarse.state ∧
        orderedTotalEnergy H.toWeighted fine.state -
            orderedTotalEnergy H.toWeighted coarse.state ≤
          (Fintype.card (OrderedFace k r) : ℝ) /
            (m : ℝ) ∧
        (∀ e, coarse.stepIndex e <
          cumulativeRegularityBudget budget i) ∧
        (∀ e, fine.stepIndex e <
          cumulativeRegularityBudget budget (i + 1)) ∧
        ((regularizedOrderedPattern
            H.toWeighted fine.state).patternCount <
              σ ^ Fintype.card (OrderedFace k r) * cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k r,
            H.IsCover D ∧
              ∀ e,
                OrderedPattern.faceDeletionDensity D e ≤
                  σ +
                    (Fintype.card fine.CellIndex : ℝ) *
                      (r : ℝ) * δ +
                    (Fintype.card (OrderedFace k r) : ℝ) /
                      ((m : ℝ) * θ ^ 2)) := by
  obtain ⟨i, hi, coarse, fine, hrefines, hgap,
      hcoarseBound, hfineBound⟩ :=
    exists_generatedOrdered_coarse_fine_pair
      H.toWeighted H.toWeighted_unitInterval hr
      ηSchedule budget hη hlong hm
  refine
    ⟨i, hi, coarse, fine, hrefines, hgap,
      hcoarseBound, hfineBound, ?_⟩
  intro hsmall
  apply
    fine.exists_generatedFineCellCover_of_coarseFinePair
      H coarse.state hrefines hr hrk hσ hθ hδ
      (ξ :=
        (Fintype.card (OrderedFace k r) : ℝ) /
          ((m : ℝ) * θ ^ 2))
  · calc
      orderedTotalEnergy H.toWeighted fine.state -
            orderedTotalEnergy H.toWeighted coarse.state ≤
          (Fintype.card (OrderedFace k r) : ℝ) /
            (m : ℝ) :=
        hgap
      _ =
          θ ^ 2 *
            ((Fintype.card (OrderedFace k r) : ℝ) /
              ((m : ℝ) * θ ^ 2)) := by
        have hmReal : (m : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hm)
        have hθsq : θ ^ 2 ≠ 0 :=
          pow_ne_zero 2 hθ.ne'
        field_simp
  · exact hsmall
  · exact hremove

end GeneratedOrderedPatternRegularization

/-! ## What one-level generated induction can prove uniformly -/

/-- A lower-rank removal threshold which is valid for every requested
deletion cost.  This is strictly stronger than
`HasUniformOrderedPatternRemoval`, where the count threshold may shrink
with the deletion cost. -/
def IsDeletionUniformOrderedRemovalThreshold
    (k r : ℕ) (c : ℝ) : Prop :=
  0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e,
                  OrderedPattern.faceDeletionDensity D e ≤ ε

/-- Rank zero has the deletion-uniform threshold one. -/
theorem isDeletionUniformOrderedRemovalThreshold_zero
    (k : ℕ) :
    IsDeletionUniformOrderedRemovalThreshold k 0 1 := by
  refine ⟨by norm_num, ?_⟩
  intro ε hε G _instFintype _instDecidableEq _instNonempty H hcount
  have hempty : H.occurrenceFinset = ∅ := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hx₀' : H.IsOccurrence x₀ :=
      (H.mem_occurrenceFinset x₀).1 hx₀
    have hall : H.occurrenceFinset = Finset.univ := by
      ext x
      simp only [H.mem_occurrenceFinset,
        Finset.mem_univ, iff_true]
      exact H.isOccurrence_all_of_rank_zero hx₀' x
    have hcountOne :
        H.toWeighted.patternCount = 1 := by
      rw [H.toWeighted_patternCount_eq, hall]
      simp
    rw [hcountOne] at hcount
    exact (lt_irrefl 1) hcount
  refine
    ⟨OrderedPattern.emptyDeletion k 0, ?_, fun e => ?_⟩
  · intro x hx
    rw [hempty] at hx
    simp at hx
  · rw [OrderedPattern.faceDeletionDensity_empty]
    exact hε.le

/-- One-level generated-cell induction closes when the lower-rank count
threshold is independent of the requested lower deletion cost.

The regularity tolerance is chosen from that fixed threshold.  Only after
the finite generated regularization is known do we choose the lower
deletion cost from its actual number of cell indices.  This order of
quantifiers is exactly what ordinary positive-rank removal does not permit.
-/
theorem hasUniformOrderedPatternRemoval_of_deletionUniformLowerThreshold
    {k r : ℕ}
    (hr : 0 < r) (hrk : r ≤ k)
    {cLower : ℝ}
    (hlower :
      IsDeletionUniformOrderedRemovalThreshold
        k (r - 1) cLower) :
    HasUniformOrderedPatternRemoval k r := by
  intro ε hε
  let σ : ℝ := ε / 2
  let q : ℕ := Fintype.card (OrderedFace k r)
  let target : ℝ := σ ^ q * cLower
  let η : ℝ :=
    target / (4 * ((q : ℝ) + 1))
  let c : ℝ := target / 2
  have hσ : 0 < σ := by
    dsimp [σ]
    linarith
  have htarget : 0 < target := by
    exact mul_pos (pow_pos hσ q) hlower.1
  have hdenη :
      0 < 4 * ((q : ℝ) + 1) := by
    positivity
  have hη : 0 < η := by
    exact div_pos htarget hdenη
  have hc : 0 < c := by
    exact div_pos htarget (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  obtain ⟨R⟩ :=
    exists_generatedOrderedPatternRegularization
      hr H.toWeighted H.toWeighted_unitInterval hη
  let cellCount : ℝ :=
    Fintype.card R.CellIndex
  let δ : ℝ :=
    ε /
      (2 * (cellCount + 1) * ((r : ℝ) + 1))
  have hcellCount : 0 ≤ cellCount := by
    positivity
  have hrReal : 0 ≤ (r : ℝ) := by
    positivity
  have hdenδ :
      0 <
        2 * (cellCount + 1) * ((r : ℝ) + 1) := by
    positivity
  have hδ : 0 < δ := by
    exact div_pos hε hdenδ
  have hηIdentity :
      (4 * ((q : ℝ) + 1)) * η = target := by
    dsimp [η]
    field_simp
  have hqη :
      (q : ℝ) * η < target / 2 := by
    have hqnonneg : 0 ≤ (q : ℝ) := by
      positivity
    nlinarith
  have hregularizedUpper :
      (regularizedOrderedPattern
          H.toWeighted R.state).patternCount ≤
        H.toWeighted.patternCount +
          (q : ℝ) * η := by
    have hdiff :
        (regularizedOrderedPattern
            H.toWeighted R.state).patternCount -
            H.toWeighted.patternCount ≤
          |H.toWeighted.patternCount -
            (regularizedOrderedPattern
              H.toWeighted R.state).patternCount| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have hclose :
        |H.toWeighted.patternCount -
            (regularizedOrderedPattern
              H.toWeighted R.state).patternCount| ≤
          (q : ℝ) * η := by
      simpa only [q] using R.count_close
    linarith
  have hsmall :
      (regularizedOrderedPattern
          H.toWeighted R.state).patternCount <
        σ ^ Fintype.card (OrderedFace k r) * cLower := by
    have hcountTarget :
        H.toWeighted.patternCount < target / 2 := by
      simpa only [c] using hcount
    have :
        (regularizedOrderedPattern
            H.toWeighted R.state).patternCount <
          target :=
      hregularizedUpper.trans_lt (by linarith)
    simpa only [target, q] using this
  have hremove :
      ∀ L : OrderedPattern G k (r - 1),
        L.toWeighted.patternCount < cLower →
          ∃ D : OrderedPattern.DeletionFamily
              (G := G) k (r - 1),
            L.IsCover D ∧
              ∀ g,
                OrderedPattern.faceDeletionDensity D g ≤ δ := by
    intro L hL
    exact hlower.2 δ hδ G L hL
  obtain ⟨D, hcover, hdensity⟩ :=
    R.exists_generatedCellCover
      H hr hrk hσ hδ.le hsmall hremove
  refine ⟨D, hcover, ?_⟩
  intro e
  have hcellProduct :
      cellCount * (r : ℝ) ≤
        (cellCount + 1) * ((r : ℝ) + 1) := by
    nlinarith [mul_nonneg hcellCount hrReal]
  have hrecursive :
      cellCount * (r : ℝ) * δ ≤ ε / 2 := by
    calc
      cellCount * (r : ℝ) * δ ≤
          (cellCount + 1) * ((r : ℝ) + 1) * δ :=
        mul_le_mul_of_nonneg_right hcellProduct hδ.le
      _ = ε / 2 := by
        dsimp [δ]
        field_simp
  have hactual :
      (Fintype.card R.CellIndex : ℝ) *
          (r : ℝ) * δ ≤
        ε / 2 := by
    simpa only [cellCount] using hrecursive
  have := (hdensity e).trans
    (add_le_add_right hactual σ)
  dsimp [σ] at this ⊢
  linarith

/-- Generated-cell induction therefore proves rank-one ordered removal
unconditionally: its recursive rank-zero threshold is the fixed value one.
-/
theorem hasUniformOrderedPatternRemoval_one_generatedCell
    (k : ℕ) (hk : 1 ≤ k) :
    HasUniformOrderedPatternRemoval k 1 := by
  apply
    hasUniformOrderedPatternRemoval_of_deletionUniformLowerThreshold
      (k := k) (r := 1) (by omega) hk
  simpa using
    isDeletionUniformOrderedRemovalThreshold_zero k

end Submission.GreenTao
