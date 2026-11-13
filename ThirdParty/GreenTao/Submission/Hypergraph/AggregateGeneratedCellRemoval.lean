import Submission.Hypergraph.OrderedCellLifting

/-!
# Aggregate generated-cell removal

The generated-cell lifting theorem in `OrderedCellLifting` applies lower-rank
removal separately to every cell and bounds each lower deletion density by
the same number `δ`.  A union bound then pays

```
card CellIndex * r * δ.
```

This file records the genuinely stronger aggregate interface.  If lower
deletions are already chosen so that, on every lower face, the *sum* of
their densities over all cells is at most `δTotal`, then their lifted union
costs only

```
r * δTotal.
```

Thus aggregation would remove the late fine-cell multiplicity completely.
The final section examines whether ordinary uniform lower-rank removal
supplies this summable family merely from an aggregate bound on the lower
cell counts.

It does not, as a consequence of its quantifiers alone.  First, the current
generator branches form an overlapping cover rather than a partition; the
branch-incidence sum can equal the entire branch cardinality.  Even if one
postulates an ideal card-free aggregate count bound, a pointwise removal
modulus need not convert total count into total deletion cost.  The
quadratic model `count < cost²` has exactly the ordinary pointwise
threshold property, while `N` cells of count `(2/N)²` have total count
`4/N → 0` but force total cost greater than two.  Finite dyadic banding is
only a restricted allocation strategy and therefore cannot bridge this
gap.  A successor proof through this route needs an additional
simultaneous/aggregate lower-removal theorem (or a quantitative modulus
strong enough to imply one), not merely
`HasUniformOrderedPatternRemoval k (r - 1)`.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## What the current cell-count API sums to -/

namespace GeneratedOrderedPatternRegularization

/-- Summing the existing individual heavy-cell estimate retains the
cardinality of the selected cell family.  No disjointness is used here. -/
theorem pow_mul_sum_lowerCellPattern_count_le_card_mul
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} {H : WeightedOrderedPattern G k r}
    {η τ : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H η)
    (hH : H.EdgeWeightsInUnitInterval)
    (hr : 0 < r) (hτ : 0 ≤ τ)
    (cells : Finset R.CellIndex)
    (hheavy :
      ∀ p ∈ cells, R.IsHeavy τ p.1) :
    τ ^ Fintype.card (OrderedFace k r) *
        (∑ p ∈ cells,
          (R.lowerCellPattern p.1 p.2).toWeighted.patternCount) ≤
      (cells.card : ℝ) *
        (regularizedOrderedPattern H R.state).patternCount := by
  rw [Finset.mul_sum]
  calc
    (∑ p ∈ cells,
        τ ^ Fintype.card (OrderedFace k r) *
          (R.lowerCellPattern p.1 p.2).toWeighted.patternCount) ≤
        ∑ _p ∈ cells,
          (regularizedOrderedPattern H R.state).patternCount := by
      apply Finset.sum_le_sum
      intro p hp
      exact
        R.pow_mul_lowerCellPattern_count_le
          hH hr hτ p.1 (hheavy p hp) p.2
    _ =
        (cells.card : ℝ) *
          (regularizedOrderedPattern H R.state).patternCount := by
      simp

end GeneratedOrderedPatternRegularization

/-! The retained generator branches are covers, not partitions. -/

/-- When the reference point belongs to every generator, the negative
branch conditions are vacuous.  Every possible branch accepts the same
point in the generated atom. -/
theorem every_generatorBranch_accepts_of_mem_all_generators
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (hF : F ⊆ booleanFaceCutSupports G r)
    (y x : Fin r → G)
    (hy : ∀ A ∈ F, y ∈ A)
    (hx : x ∈ (FacePartition.generatedBy F).part y) :
    ∀ (w : GeneratorBranch F) (i : Fin r),
      eraseCoordinate i x ∈
        lowerGeneratorCell F y w i := by
  classical
  have hsignature :
      ∀ A ∈ F, (y ∈ A ↔ x ∈ A) :=
    (FacePartition.mem_part_generatedBy_iff F y x).1 hx
  intro w i
  rw [mem_lowerGeneratorCell]
  intro A
  constructor
  · intro hyA
    have hxA : x ∈ A.1 :=
      (hsignature A.1 A.2).1 hyA
    have hsupport :
        booleanFaceCutSupport
            (representingBooleanFaceCutAssignment G r A.1) =
          A.1 :=
      booleanFaceCutSupport_representing (hF A.2)
    have hxSupport :
        x ∈ booleanFaceCutSupport
          (representingBooleanFaceCutAssignment G r A.1) := by
      simpa only [hsupport] using hxA
    exact
      (mem_booleanFaceCutSupport
        (representingBooleanFaceCutAssignment G r A.1) x).1
        hxSupport i
  · intro hyNot
    exact (hyNot (hy A.1 A.2)).elim

/-- Hence the branch-incidence sum can equal the full branch cardinality
`r ^ F.card`; it is not bounded by one. -/
theorem sum_generatorBranch_indicator_eq_card_of_mem_all_generators
    {G : Type*} [Fintype G] [DecidableEq G]
    {r : ℕ}
    (F : Finset (BooleanCutTest (Fin r → G)))
    (hF : F ⊆ booleanFaceCutSupports G r)
    (y x : Fin r → G)
    (hy : ∀ A ∈ F, y ∈ A)
    (hx : x ∈ (FacePartition.generatedBy F).part y) :
    (∑ w : GeneratorBranch F,
        if (∀ i : Fin r,
          eraseCoordinate i x ∈
            lowerGeneratorCell F y w i)
        then (1 : ℝ) else 0) =
      (r ^ F.card : ℕ) := by
  classical
  have hall :
      ∀ w : GeneratorBranch F,
        ∀ i : Fin r,
          eraseCoordinate i x ∈
            lowerGeneratorCell F y w i :=
    every_generatorBranch_accepts_of_mem_all_generators
      F hF y x hy hx
  calc
    (∑ w : GeneratorBranch F,
        if (∀ i : Fin r,
          eraseCoordinate i x ∈
            lowerGeneratorCell F y w i)
        then (1 : ℝ) else 0) =
        ∑ _w : GeneratorBranch F, (1 : ℝ) := by
      apply Fintype.sum_congr
      intro w
      rw [if_pos (hall w)]
    _ = (r ^ F.card : ℕ) := by
      simp

namespace OrderedPattern

/-- Exact union-bound form of lower-deletion lifting, before replacing all
lower-face densities by one common bound. -/
theorem faceDeletionDensity_liftLowerDeletion_le_sum
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k (r - 1))
    (e : OrderedFace k r) :
    faceDeletionDensity (liftLowerDeletion D) e ≤
      ∑ i : Fin r,
        faceDeletionDensity D (eraseOrderedFace e i) := by
  unfold faceDeletionDensity
  have hdenom :
      (0 : ℝ) <
        Fintype.card (Fin r → G) := by
    positivity
  calc
    ((liftLowerDeletion D e).card : ℝ) /
          Fintype.card (Fin r → G) ≤
        (∑ i : Fin r,
          (deletionCylinder D e i).card : ℕ) /
            Fintype.card (Fin r → G) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast card_liftLowerDeletion_le D e
      · exact hdenom.le
    _ =
        ∑ i : Fin r,
          ((deletionCylinder D e i).card : ℝ) /
            Fintype.card (Fin r → G) := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ =
        ∑ i : Fin r,
          faceDeletionDensity D
            (eraseOrderedFace e i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact deletionCylinder_density_eq D e i

end OrderedPattern

namespace GeneratedOrderedPatternRegularization

/-- **Aggregate generated-cell lifting.**

The lower deletion attached to each active heavy cell may have a different
density.  Only the sum of those densities on each lower ordered face is
charged.  Low structured atoms and inactive cells are handled exactly as
in `exists_generatedCellCover_of_activeLowerCellCounts`.
-/
theorem exists_generatedCellCover_of_aggregateLowerDeletions
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    {η τ δTotal ξ : ℝ}
    (R : GeneratedOrderedPatternRegularization
      G k r H.toWeighted η)
    (hr : 0 < r) (hrk : r ≤ k)
    (hτ : 0 < τ)
    (active : R.CellIndex → Prop)
    (exceptionalDeletion :
      OrderedPattern.DeletionFamily (G := G) k r)
    (hexceptionalDensity :
      ∀ e,
        OrderedPattern.faceDeletionDensity
          exceptionalDeletion e ≤ ξ)
    (hexceptionalCover :
      ∀ (a : R.TopAtomChoice) (w : R.BranchSystem)
          (x : Fin k → G),
        R.IsHeavy τ a →
        (R.lowerCellPattern a w).IsOccurrence x →
        ¬active (a, w) →
          ∃ e,
            orderedFaceTuple e x ∈
              exceptionalDeletion e)
    (lowerDeletion :
      R.CellIndex →
        OrderedPattern.DeletionFamily
          (G := G) k (r - 1))
    (hlowerCover :
      ∀ (a : R.TopAtomChoice),
        R.IsHeavy τ a →
          ∀ (w : R.BranchSystem),
            active (a, w) →
              (R.lowerCellPattern a w).IsCover
                (lowerDeletion (a, w)))
    (hlowerDensity :
      ∀ g,
        (∑ p : R.CellIndex,
          OrderedPattern.faceDeletionDensity
            (lowerDeletion p) g) ≤
          δTotal) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k r,
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤
            τ + (r : ℝ) * δTotal + ξ := by
  classical
  let liftedCellDeletion :
      R.CellIndex →
        OrderedPattern.DeletionFamily (G := G) k r :=
    fun p =>
      OrderedPattern.liftLowerDeletion
        (lowerDeletion p)
  let cellDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.unionDeletion liftedCellDeletion
  let lowDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.lowStructuredDeletion
      H R.state τ
  let baseComponents :
      Bool →
        OrderedPattern.DeletionFamily (G := G) k r :=
    fun b => if b then cellDeletion else lowDeletion
  let baseDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.unionDeletion baseComponents
  let components :
      Bool →
        OrderedPattern.DeletionFamily (G := G) k r :=
    fun b =>
      if b then exceptionalDeletion else baseDeletion
  let totalDeletion :
      OrderedPattern.DeletionFamily (G := G) k r :=
    OrderedPattern.unionDeletion components
  have hcellDensity (e : OrderedFace k r) :
      OrderedPattern.faceDeletionDensity
          cellDeletion e ≤
        (r : ℝ) * δTotal := by
    calc
      OrderedPattern.faceDeletionDensity
          cellDeletion e ≤
          ∑ p : R.CellIndex,
            OrderedPattern.faceDeletionDensity
              (liftedCellDeletion p) e := by
        exact
          OrderedPattern.faceDeletionDensity_unionDeletion_le
            liftedCellDeletion e
      _ ≤
          ∑ p : R.CellIndex,
            ∑ i : Fin r,
              OrderedPattern.faceDeletionDensity
                (lowerDeletion p)
                (eraseOrderedFace e i) := by
        apply Finset.sum_le_sum
        intro p _hp
        exact
          OrderedPattern.faceDeletionDensity_liftLowerDeletion_le_sum
            (lowerDeletion p) e
      _ =
          ∑ i : Fin r,
            ∑ p : R.CellIndex,
              OrderedPattern.faceDeletionDensity
                (lowerDeletion p)
                (eraseOrderedFace e i) := by
        exact Finset.sum_comm
      _ ≤ ∑ _i : Fin r, δTotal := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hlowerDensity (eraseOrderedFace e i)
      _ = (r : ℝ) * δTotal := by
        simp
  have hbaseDensity (e : OrderedFace k r) :
      OrderedPattern.faceDeletionDensity
          baseDeletion e ≤
        τ + (r : ℝ) * δTotal := by
    calc
      OrderedPattern.faceDeletionDensity
          baseDeletion e ≤
          ∑ b : Bool,
            OrderedPattern.faceDeletionDensity
              (baseComponents b) e := by
        exact
          OrderedPattern.faceDeletionDensity_unionDeletion_le
            baseComponents e
      _ =
          OrderedPattern.faceDeletionDensity lowDeletion e +
            OrderedPattern.faceDeletionDensity cellDeletion e := by
        simp [baseComponents]
        ring
      _ ≤ τ + (r : ℝ) * δTotal :=
        add_le_add
          (OrderedPattern.faceDeletionDensity_lowStructuredDeletion_le
            H R.state hτ.le e)
          (hcellDensity e)
  have htotalDensity (e : OrderedFace k r) :
      OrderedPattern.faceDeletionDensity
          totalDeletion e ≤
        τ + (r : ℝ) * δTotal + ξ := by
    calc
      OrderedPattern.faceDeletionDensity
          totalDeletion e ≤
          ∑ b : Bool,
            OrderedPattern.faceDeletionDensity
              (components b) e := by
        exact
          OrderedPattern.faceDeletionDensity_unionDeletion_le
            components e
      _ =
          OrderedPattern.faceDeletionDensity baseDeletion e +
            OrderedPattern.faceDeletionDensity
              exceptionalDeletion e := by
        simp [components]
        ring
      _ ≤
          (τ + (r : ℝ) * δTotal) + ξ :=
        add_le_add (hbaseDensity e)
          (hexceptionalDensity e)
  refine ⟨totalDeletion, ?_, htotalDensity⟩
  intro x hx
  have hxocc : H.IsOccurrence x :=
    (H.mem_occurrenceFinset x).1 hx
  by_cases hlow :
      ∃ e : OrderedFace k r,
        orderedFaceTuple e x ∈ lowDeletion e
  · obtain ⟨e, he⟩ := hlow
    have hbase :
        orderedFaceTuple e x ∈ baseDeletion e := by
      apply
        (OrderedPattern.mem_unionDeletion
          baseComponents e _).2
      refine ⟨false, ?_⟩
      simpa [baseComponents] using he
    refine ⟨e,
      (OrderedPattern.mem_unionDeletion
        components e _).2 ⟨false, ?_⟩⟩
    simpa [components] using hbase
  · push Not at hlow
    let a : R.TopAtomChoice :=
      R.topAtomChoiceOf x
    have ha : R.IsHeavy τ a := by
      intro e
      have hmem :
          orderedFaceTuple e x ∈ (a e).1 :=
        R.mem_topAtomChoiceOf x e
      rw [← R.regularized_edgeWeight_eq_atomEdgeWeight
        a e x hmem]
      exact
        OrderedPattern.regularized_edgeWeight_ge_of_not_mem_lowDeletion
          H R.state τ e (orderedFaceTuple e x)
          (hxocc e) (hlow e)
    have hbranch :
        ∃ w : R.BranchSystem,
          R.IsInAtomBranch a w x :=
      (R.mem_all_topAtoms_iff_exists_branchSystem
        hr a x).1
        (fun e => R.mem_topAtomChoiceOf x e)
    obtain ⟨w, hw⟩ := hbranch
    have hlowerOccurrence :
        (R.lowerCellPattern a w).IsOccurrence x :=
      (R.lowerCellPattern_isOccurrence_iff
        a w x).2 hw
    by_cases hactive : active (a, w)
    · have hlowerCover :
          (R.lowerCellPattern a w).IsCover
            (lowerDeletion (a, w)) :=
        hlowerCover a ha w hactive
      obtain ⟨e, he⟩ :=
        OrderedPattern.lowerCover_lifts
          hr hrk (R.lowerCellPattern a w)
          (lowerDeletion (a, w))
          hlowerCover hlowerOccurrence
      have hcell :
          orderedFaceTuple e x ∈ cellDeletion e := by
        apply
          (OrderedPattern.mem_unionDeletion
            liftedCellDeletion e _).2
        exact ⟨(a, w), he⟩
      have hbase :
          orderedFaceTuple e x ∈ baseDeletion e := by
        apply
          (OrderedPattern.mem_unionDeletion
            baseComponents e _).2
        refine ⟨true, ?_⟩
        simpa [baseComponents] using hcell
      refine ⟨e,
        (OrderedPattern.mem_unionDeletion
          components e _).2 ⟨false, ?_⟩⟩
      simpa [components] using hbase
    · obtain ⟨e, he⟩ :=
        hexceptionalCover a w x ha
          hlowerOccurrence hactive
      refine ⟨e,
        (OrderedPattern.mem_unionDeletion
          components e _).2 ⟨true, ?_⟩⟩
      simpa [components] using he

end GeneratedOrderedPatternRegularization

/-! ## Ordinary pointwise removal does not imply aggregate allocation -/

/-- Abstract scalar form of the quantifiers supplied by ordinary uniform
removal: for every positive requested cost there is some positive count
threshold which makes one problem admissible at that cost. -/
def HasPointwiseCountCostThreshold
    (admissible : ℝ → ℝ → Prop) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, 0 ≤ t → t < c →
        admissible t δ

/-- The aggregate conclusion needed by the bundled lifting theorem:
arbitrarily many problems of small *total* count have individual costs
whose sum is bounded independently of their number. -/
def HasAggregateCountCostAllocation
    (admissible : ℝ → ℝ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ), 0 < N →
        ∀ t : Fin N → ℝ,
          (∀ i, 0 ≤ t i) →
          (∑ i, t i) < c →
            ∃ δ : Fin N → ℝ,
              (∀ i, admissible (t i) (δ i)) ∧
              (∑ i, δ i) ≤ ε

/-- A model pointwise modulus with the common quadratic shape
`count < cost²`. -/
def QuadraticCountCostAdmissible
    (t δ : ℝ) : Prop :=
  0 ≤ δ ∧ t < δ ^ 2

/-- The quadratic model has the ordinary pointwise threshold property. -/
theorem hasPointwiseCountCostThreshold_quadratic :
    HasPointwiseCountCostThreshold
      QuadraticCountCostAdmissible := by
  intro δ hδ
  refine ⟨δ ^ 2, sq_pos_of_pos hδ, ?_⟩
  intro t _ht hsmall
  exact ⟨hδ.le, hsmall⟩

/-- For `N` equal-count problems, quadratic admissibility forces total
cost strictly larger than `N` times the square root scale. -/
theorem sum_cost_gt_of_quadraticCountCost
    {N : ℕ} (hN : 0 < N)
    {d : ℝ} (hd : 0 < d)
    (δ : Fin N → ℝ)
    (hδ :
      ∀ i,
        QuadraticCountCostAdmissible
          (d ^ 2) (δ i)) :
    (N : ℝ) * d < ∑ i, δ i := by
  have hdi : ∀ i, d < δ i := by
    intro i
    exact
      (sq_lt_sq₀ hd.le (hδ i).1).mp
        (hδ i).2
  have hsumPos :
      0 < ∑ i : Fin N, (δ i - d) := by
    apply Finset.sum_pos'
    · intro i _hi
      exact sub_nonneg.mpr (hdi i).le
    · let i : Fin N := ⟨0, hN⟩
      exact
        ⟨i, Finset.mem_univ i,
          sub_pos.mpr (hdi i)⟩
  have hdiff :
      0 <
        (∑ i : Fin N, δ i) -
          ∑ _i : Fin N, d := by
    rw [← Finset.sum_sub_distrib]
    exact hsumPos
  have hconst :
      (∑ _i : Fin N, d) = (N : ℝ) * d := by
    simp
  rw [hconst] at hdiff
  linarith

/-- **Aggregate-allocation obstruction.**

Even an exact aggregate bound on the sum of the problem counts does not
follow from the ordinary pointwise threshold quantifiers.  In the
quadratic model, take `N` problems each of count `(2/N)²`: their total count
is `4/N`, tending to zero, while every admissible allocation has total
cost greater than two.

Since dyadic banding is only a particular way to choose the individual
costs, it cannot derive aggregate removal from the pointwise interface
without an additional quantitative or simultaneous-removal hypothesis.
-/
theorem not_hasAggregateCountCostAllocation_quadratic :
    ¬HasAggregateCountCostAllocation
      QuadraticCountCostAdmissible := by
  intro haggregate
  obtain ⟨c, hc, hallocate⟩ :=
    haggregate 1 (by norm_num)
  obtain ⟨N, hNlarge⟩ :=
    exists_nat_gt (4 / c)
  have hfourDivPos : 0 < 4 / c := by
    exact div_pos (by norm_num) hc
  have hNreal : 0 < (N : ℝ) :=
    hfourDivPos.trans hNlarge
  have hN : 0 < N := by
    exact_mod_cast hNreal
  let d : ℝ := 2 / (N : ℝ)
  let t : Fin N → ℝ := fun _ => d ^ 2
  have hd : 0 < d := by
    exact div_pos (by norm_num) hNreal
  have hfourLt : (4 : ℝ) < (N : ℝ) * c := by
    exact (div_lt_iff₀ hc).mp hNlarge
  have hfourDivLt : (4 : ℝ) / (N : ℝ) < c := by
    apply (div_lt_iff₀ hNreal).2
    simpa [mul_comm] using hfourLt
  have hcount :
      (∑ i : Fin N, t i) < c := by
    calc
      (∑ i : Fin N, t i) =
          (N : ℝ) * d ^ 2 := by
        simp [t]
      _ = 4 / (N : ℝ) := by
        dsimp [d]
        field_simp
        ring
      _ < c := hfourDivLt
  obtain ⟨δ, hδ, hcost⟩ :=
    hallocate N hN t
      (fun _i => by
        dsimp [t]
        exact sq_nonneg d)
      hcount
  have hcostLower :
      (N : ℝ) * d < ∑ i, δ i := by
    apply
      sum_cost_gt_of_quadraticCountCost
        hN hd δ
    intro i
    simpa only [t] using hδ i
  have hNd : (N : ℝ) * d = 2 := by
    dsimp [d]
    field_simp
  rw [hNd] at hcostLower
  linarith

end Submission.GreenTao
