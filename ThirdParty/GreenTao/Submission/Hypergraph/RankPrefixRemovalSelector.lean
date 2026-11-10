import Submission.Hypergraph.RankPrefixSelectedRemoval

/-!
# Ambient-independent selectors for rank-prefix ordered removal

The global-stage and all-landing removal schedules are too strong: their
rank-one and rank-two specializations are formally contradictory.  The
rank-prefix counting theorem and the exact selected-gap cleaner need much
less.  They only use the tolerance, upper complexity, and literal energy
gap of the certificate actually returned by regularity.

This file separates the structural and numerical quantifiers accordingly.

* `RankPrefixRegularitySelector` is the ambient-independent structural
  selector.  It fixes the tolerance, budget, and horizon schedules before
  seeing the ambient finite type, then returns one coarse-target certificate.
  This interface is unconditionally inhabited.
* `RankPrefixSelectedRemovalCompatibility` is precisely the numerical
  payload at that selected certificate.  It retains the triangular
  rank-prefix thresholds and the literal selected gaps.
* `CorrelatedRankPrefixRemovalSelector` chooses the certificate and its
  compatible payload together.  Existence of these correlated selectors
  implies uniform ordered-pattern removal.

Thus the remaining dense-side parameter theorem is isolated without asking
for a false inequality at an unselected landing.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Weighted one-rank energy stopping -/

/-- Weighted adjacent-increment pigeonhole.

If the endpoint energy budget is paid by the total weighted allowance, one
adjacent increment is small relative to its own positive weight.  Taking the
weights to be the selected defect thresholds is the exact one-rank mechanism
needed to control a literal term `gap / β`; it does not replace the gap by a
uniform reciprocal horizon. -/
theorem exists_adjacent_real_sub_div_le_of_weighted_budget
    (E weight : ℕ → ℝ)
    {length : ℕ} (hlength : 0 < length)
    {B ξ : ℝ}
    (hE0 : 0 ≤ E 0)
    (hElast : E length ≤ B)
    (hweight :
      ∀ i, i < length → 0 < weight i)
    (hbudget :
      B ≤
        ∑ i ∈ Finset.range length,
          ξ * weight i) :
    ∃ i : ℕ, i < length ∧
      (E (i + 1) - E i) / weight i ≤ ξ := by
  have htel :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ i ∈ Finset.range length,
          ξ * weight i := by
    rw [htel]
    exact (by linarith : E length - E 0 ≤ B).trans hbudget
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hlength⟩ hsum
  have hi' : i < length :=
    Finset.mem_range.mp hi
  refine ⟨i, hi', ?_⟩
  exact (div_le_iff₀ (hweight i hi')).2 hsmall

/-- One fixed-upper regularity step selected by a weighted energy stopping
rule.  The selected literal gap is divided by its own weight in the
certificate, rather than enlarged to `card / length`.

This is the concrete local construction needed by a future coupled
rank-prefix selector.  The remaining all-rank issue is to build the weights
and lower-rank schedules coherently along the selected top-down path. -/
structure WeightedFixedUpperLayerCoarseFine
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (tolerance : ℕ → ℝ) (budget : ℕ → ℕ)
    (weight : ℕ → ℝ) (length : ℕ) (ξ : ℝ) where
  index : ℕ
  index_lt : index < length
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper (tolerance index)
  gap_nonneg :
    0 ≤ orderedLayerAtomEnergy fine upper -
      orderedLayerAtomEnergy coarse upper
  gap_div_weight_le :
    (orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper) /
      weight index ≤ ξ
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        fixedUpperLayerComplexityFactor
            j budget index *
          FacePartition.complexity (initial e)
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        fixedUpperLayerComplexityFactor
            j budget (index + 1) *
          FacePartition.complexity (initial e)

/-- Existence of the weighted fixed-upper stopping certificate. -/
theorem WeightedFixedUpperLayerCoarseFine.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (tolerance : ℕ → ℝ) (budget : ℕ → ℕ)
    (weight : ℕ → ℝ)
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    {length : ℕ} (hlength : 0 < length)
    {ξ : ℝ}
    (hweight :
      ∀ i, i < length → 0 < weight i)
    (henergy :
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) ≤
        ∑ i ∈ Finset.range length,
          ξ * weight i) :
    Nonempty
      (WeightedFixedUpperLayerCoarseFine
        G k j initial upper tolerance budget
          weight length ξ) := by
  let tower :=
    fixedUpperLayerRegularityTower
      initial upper tolerance budget
        htolerance hbudget
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_real_sub_div_le_of_weighted_budget
      (fun n =>
        orderedLayerAtomEnergy (tower n) upper)
      weight hlength
      (orderedLayerAtomEnergy_nonneg
        (tower 0) upper)
      (orderedLayerAtomEnergy_le_card
        (tower length) upper)
      hweight henergy
  refine ⟨{
    index := i
    index_lt := hi
    coarse := tower i
    fine := tower (i + 1)
    refines := ?_
    coarse_refines_initial := ?_
    fine_regular := ?_
    gap_nonneg := ?_
    gap_div_weight_le := hgap
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · exact
      fixedUpperLayerRegularityTower_refines
        initial upper tolerance budget
          htolerance hbudget i
  · exact
      fixedUpperLayerRegularityTower_refines_initial
        initial upper tolerance budget
          htolerance hbudget i
  · exact
      fixedUpperLayerRegularityTower_regular
        initial upper tolerance budget
          htolerance hbudget i
  · exact sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fixedUpperLayerRegularityTower_refines
          initial upper tolerance budget
            htolerance hbudget i)
        upper)
  · exact
      complexity_fixedUpperLayerRegularityTower_le
        initial upper tolerance budget
          htolerance hbudget i
  · exact
      complexity_fixedUpperLayerRegularityTower_le
        initial upper tolerance budget
          htolerance hbudget (i + 1)

/-! ## An unconditionally inhabited structural selector -/

/-- Ambient-independent schedules together with a canonical coarse-target
regularity certificate over every finite nonempty ambient type.

No removal margin is built into this structure.  It is the smallest
structural selector on top of which an honest selected-certificate
parameter theorem can be stated. -/
structure RankPrefixRegularitySelector (k r : ℕ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  select :
    ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
      (initial : OrderedPartitionComplex G k r),
      CoarseTargetOrderedComplexRegularityCertificate
        G k r initial tolerance budget length

/-- Any positive schedules satisfying the one-step regularity budget and
horizon hypotheses give an ambient-independent selector by classical choice
from coarse-target regularity. -/
noncomputable def rankPrefixRegularitySelectorOfSchedules
    (k r : ℕ)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 < tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    RankPrefixRegularitySelector k r where
  tolerance := tolerance
  budget := budget
  length := length
  tolerance_pos := htolerance
  budget_spec := hbudget
  length_pos := hlength
  select := by
    intro G _instFintype _instDecidableEq _instNonempty initial
    exact Classical.choice
      (CoarseTargetOrderedComplexRegularityCertificate.nonempty
        initial tolerance budget length
        (fun j n => (htolerance j n).le)
        hbudget hlength)

/-- A concrete structural selector: tolerance and horizon are one, and the
standard ceiling budget pays for the one preliminary-regularity pass. -/
noncomputable def unitRankPrefixRegularitySelector
    (k r : ℕ) :
    RankPrefixRegularitySelector k r :=
  rankPrefixRegularitySelectorOfSchedules
    k r
    (fun _j _n => 1)
    (fun j _n =>
      orderedRemovalRegularityBudget k j.1 1)
    (fun _j => 1)
    (by
      intro j n
      norm_num)
    (by
      intro j n
      simpa using
        (orderedRemovalRegularityBudget_spec
          (k := k) (j := j.1)
          (τ := (1 : ℝ)) (by norm_num)))
    (by
      intro j
      norm_num)

/-- The structural selector problem itself has no existence gap. -/
theorem rankPrefixRegularitySelector_nonempty
    (k r : ℕ) :
    Nonempty (RankPrefixRegularitySelector k r) :=
  ⟨unitRankPrefixRegularitySelector k r⟩

/-! ## Numerical compatibility at the selected certificate -/

/-- The exact rank-prefix counting and literal-gap cleaning data attached
to one selected coarse-target certificate.

The positive number `c` is chosen before the ambient type.  The final field
requires it to lie below the selected half-density barrier.  All remaining
fields are exactly the hypotheses of
`exists_orderedPatternRemoval_of_rankPrefixSelectedBounds`. -/
structure RankPrefixSelectedRemovalCompatibility
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length)
    (ξ c : ℝ) where
  densityFloor : ℕ → ℝ
  defectThreshold : ℕ → ℝ
  upperBound : Fin r → ℕ
  densityFloor_pos : ∀ m, 0 < densityFloor m
  densityFloor_le_one : ∀ m, densityFloor m ≤ 1
  defectThreshold_pos : ∀ m, 0 < defectThreshold m
  defectThreshold_rankPrefix :
    ∀ j,
      defectThreshold j ≤
        (densityFloor j / 4) ^ 2 *
          configurationRankPrefixBarrier
            k r densityFloor j
  tolerance_rankPrefix :
    ∀ e : PositiveOrderedFace k r,
      selectedOrderedComplexTolerance
          tolerance R.index e.lowerRank ≤
        (densityFloor e.rank / 4) *
          configurationRankPrefixBarrier
            k r densityFloor e.rank
  coarse_upper_complexity :
    ∀ (j : Fin r)
        (e : OrderedFace k (j.1 + 1)),
      FacePartition.complexity
          (R.coarse.partition j.succ e) ≤
        upperBound j
  deletion_margin :
    (∑ q : OrderedPositiveSubface r,
      ((upperBound q.1 : ℝ) *
          densityFloor (q.1.1 + 1) +
        R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
          defectThreshold (q.1.1 + 1))) ≤
      ξ
  count_threshold_le :
    c ≤
      configurationHalfDensityBarrier
        (k := k) (r := r) densityFloor Finset.univ

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Selected rank-prefix compatibility gives the semantic removal cover.
Only the certificate actually selected by the structural regularity
argument is used. -/
theorem exists_orderedPatternRemoval_of_rankPrefixCompatibility
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrank : n + 1 ≤ k)
    {initial : OrderedPartitionComplex G k (n + 1)}
    {tolerance : (j : Fin (n + 1)) → ℕ → ℝ}
    {budget : (j : Fin (n + 1)) → ℕ → ℕ}
    {length : Fin (n + 1) → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k (n + 1) initial tolerance budget length)
    (H : OrderedPattern G k (n + 1))
    (hinitial :
      R.coarse.Refines (orderedPatternInitialComplex H))
    {ξ c : ℝ}
    (C : RankPrefixSelectedRemovalCompatibility R ξ c)
    (hcount : H.toWeighted.patternCount < c) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k (n + 1),
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  apply
    R.exists_orderedPatternRemoval_of_rankPrefixSelectedBounds
      hrank H hinitial
      C.densityFloor C.defectThreshold
      C.densityFloor_pos C.densityFloor_le_one
      C.defectThreshold_pos
      C.defectThreshold_rankPrefix
      C.tolerance_rankPrefix
      C.upperBound C.coarse_upper_complexity
      C.deletion_margin
  exact hcount.trans_le C.count_threshold_le

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Correlated removal selectors -/

/-- Ambient-independent schedules and a positive count threshold whose
certificate is selected together with its rank-prefix numerical payload.

The `select` field is deliberately correlated: it does not require the
payload at every point of the finite stage box, or even at every landing of
an adaptive tree. -/
structure CorrelatedRankPrefixRemovalSelector
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  countThreshold : ℝ
  countThreshold_pos : 0 < countThreshold
  select :
    ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
      (initial : OrderedPartitionComplex G k r),
      (∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound) →
      ∃ R : CoarseTargetOrderedComplexRegularityCertificate
          G k r initial tolerance budget length,
        Nonempty
          (RankPrefixSelectedRemovalCompatibility
            R ξ countThreshold)

/-- Existence of a correlated selected-certificate payload for every
positive deletion allowance. -/
def HasCorrelatedRankPrefixRemovalSelectors
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (CorrelatedRankPrefixRemovalSelector
        k r initialBound ξ)

/-- Correlated rank-prefix selectors close uniform ordered-pattern removal.
This is the strongest honest ambient-independent endpoint supplied here:
no condition is imposed on an unselected regularity landing. -/
theorem hasUniformOrderedPatternRemoval_succ_of_correlatedRankPrefixSelectors
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hselectors :
      HasCorrelatedRankPrefixRemovalSelectors
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  let S : CorrelatedRankPrefixRemovalSelector
      k (n + 1) 2 ξ :=
    Classical.choice (hselectors ξ hξ)
  refine ⟨S.countThreshold, S.countThreshold_pos, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty
    H hcount
  obtain ⟨R, ⟨C⟩⟩ :=
    S.select G (orderedPatternInitialComplex H)
      (complexity_orderedPatternInitialComplex_le_two H)
  exact
    R.exists_orderedPatternRemoval_of_rankPrefixCompatibility
      hrank H R.coarse_refines_initial C hcount

/-! ## The exact remaining extension of an inhabited selector -/

/-- Numerical removal margins extending one already inhabited structural
selector.  This formulation makes the remaining quantifier explicit:
`S`, `c`, and the schedules are fixed before `G` and `initial`, while the
payload may use the literal tolerance, upper complexity, and energy gaps of
`S.select G initial`. -/
structure RankPrefixRegularitySelector.RemovalMarginExtension
    {k r : ℕ}
    (S : RankPrefixRegularitySelector k r)
    (initialBound : ℕ) (ξ c : ℝ) : Prop where
  countThreshold_pos : 0 < c
  compatible :
    ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
      (initial : OrderedPartitionComplex G k r),
      (∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound) →
      Nonempty
        (RankPrefixSelectedRemovalCompatibility
          (S.select G initial) ξ c)

/-- A numerical margin extension of an inhabited structural selector
produces the correlated selector used by removal. -/
noncomputable def
    RankPrefixRegularitySelector.RemovalMarginExtension.toCorrelatedSelector
    {k r initialBound : ℕ} {ξ c : ℝ}
    {S : RankPrefixRegularitySelector k r}
    (E : S.RemovalMarginExtension initialBound ξ c) :
    CorrelatedRankPrefixRemovalSelector
      k r initialBound ξ where
  tolerance := S.tolerance
  budget := S.budget
  length := S.length
  tolerance_pos := S.tolerance_pos
  budget_spec := S.budget_spec
  length_pos := S.length_pos
  countThreshold := c
  countThreshold_pos := E.countThreshold_pos
  select := by
    intro G _instFintype _instDecidableEq _instNonempty
      initial hinitial
    exact ⟨S.select G initial, E.compatible G initial hinitial⟩

/-- Exact factored dense-side obligation.  Structural selector existence is
already unconditional; it remains to attach a positive uniform threshold
and selected rank-prefix margins for every deletion allowance. -/
def HasRankPrefixRemovalMarginExtensions
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    ∃ (S : RankPrefixRegularitySelector k r) (c : ℝ),
      Nonempty
        (S.RemovalMarginExtension initialBound ξ c)

/-- The factored margin-extension obligation is sufficient for uniform
ordered-pattern removal. -/
theorem hasUniformOrderedPatternRemoval_succ_of_rankPrefixMarginExtensions
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hextensions :
      HasRankPrefixRemovalMarginExtensions
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  apply
    hasUniformOrderedPatternRemoval_succ_of_correlatedRankPrefixSelectors
      k n hrank
  intro ξ hξ
  obtain ⟨S, c, ⟨E⟩⟩ := hextensions ξ hξ
  exact ⟨E.toCorrelatedSelector⟩

end Submission.GreenTao
