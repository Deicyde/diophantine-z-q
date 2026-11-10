import Submission.Hypergraph.CoarseTargetRemovalBridge
import Submission.Hypergraph.OrderedRemovalAssembly

/-!
# Stage-indexed schedules for coarse-target ordered removal

The coarse-target certificate selects one tower index independently at every
rank.  This file packages the exact ambient-independent numerical interface
needed after that selection.  A stage index is represented by

```
(j : Fin r) → Fin (length j),
```

so the finite bounded-index condition is built into its type.  Density,
defect-threshold, and defect-error parameters may depend on the whole selected
index vector.  The count threshold itself is uniform over all such vectors,
as required by `HasUniformOrderedPatternRemoval`.

The final theorem is conditional: it reduces ordered removal to the existence
of these schedules, but does not assert that a compatible schedule exists.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Finite selected-index vectors and their coarse complexity bound -/

/-- A complete vector of tower indices, each already bounded by the
corresponding energy-selection length. -/
abbrev CoarseTargetStageIndex
    {r : ℕ} (length : Fin r → ℕ) :=
  (j : Fin r) → Fin (length j)

/-- Turn the index field of a coarse-target certificate into its finite
bounded stage-index vector. -/
def CoarseTargetOrderedComplexRegularityCertificate.stageIndex
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    CoarseTargetStageIndex length :=
  fun j => ⟨R.index j, R.index_lt j⟩

/-- Stage-local global bound for the selected coarse complex.  At a non-top
rank it uses the complexity factor at the selected coarse endpoint `index j`,
not the following fine endpoint.  The leading `1` covers the unchanged top
layer. -/
def coarseTargetSelectedCoarseComplexityBound
    (r initialBound : ℕ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (index : CoarseTargetStageIndex length) : ℕ :=
  initialBound *
    (1 +
      ∑ j : Fin r,
        fixedUpperLayerComplexityFactor
          j.1 (budget j) (index j).1)

/-- One selected rank factor is dominated by the global selected coarse
complexity factor. -/
theorem fixedUpperLayerComplexityFactor_le_selectedCoarseBoundFactor
    {r : ℕ}
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (index : CoarseTargetStageIndex length)
    (j : Fin r) :
    fixedUpperLayerComplexityFactor
        j.1 (budget j) (index j).1 ≤
      1 +
        ∑ i : Fin r,
          fixedUpperLayerComplexityFactor
            i.1 (budget i) (index i).1 := by
  have hsum :
      fixedUpperLayerComplexityFactor
          j.1 (budget j) (index j).1 ≤
        ∑ i : Fin r,
          fixedUpperLayerComplexityFactor
            i.1 (budget i) (index i).1 := by
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (fixedUpperLayerComplexityFactor
          i.1 (budget i) (index i).1))
      (Finset.mem_univ j)
  omega

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Every partition of the selected coarse complex is bounded by the
stage-indexed coarse bound, including the unchanged top layer. -/
theorem coarse_complexity_le_selectedBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (hinitial :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j e) ≤ initialBound) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          (R.coarse.partition j e) ≤
        coarseTargetSelectedCoarseComplexityBound
          r initialBound budget length R.stageIndex := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      have htop := congrFun R.coarse_topLayer_eq e
      simp only [OrderedPartitionComplex.topLayer] at htop
      rw [htop]
      apply (hinitial (Fin.last r) e).trans
      unfold coarseTargetSelectedCoarseComplexityBound
      exact Nat.le_mul_of_pos_right initialBound
        (by positivity)
  | cast i =>
      intro e
      have hcertificate := R.coarse_complexity i e
      have hfactorBound :
          fixedUpperLayerComplexityFactor
              i.1 (budget i) (R.stageIndex i).1 ≤
            1 +
              ∑ q : Fin r,
                fixedUpperLayerComplexityFactor
                  q.1 (budget q) (R.stageIndex q).1 :=
        fixedUpperLayerComplexityFactor_le_selectedCoarseBoundFactor
          budget length R.stageIndex i
      calc
        FacePartition.complexity
            (R.coarse.partition i.castSucc e) ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (R.index i) *
              FacePartition.complexity
                (initial.partition i.castSucc e) :=
          hcertificate
        _ ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (R.index i) *
              initialBound :=
          Nat.mul_le_mul_left _
            (hinitial i.castSucc e)
        _ ≤
            coarseTargetSelectedCoarseComplexityBound
              r initialBound budget length R.stageIndex := by
          unfold coarseTargetSelectedCoarseComplexityBound
          simpa [stageIndex, Nat.mul_comm] using
            Nat.mul_le_mul_left initialBound hfactorBound

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Certificate-level compatibility -/

/-- The exact numerical facts needed to turn one coarse-target regularity
certificate into a removal family. -/
structure IsCoarseTargetRemovalCertificateCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (ξ c ρ β δ : ℝ) (coarseBound : ℕ) : Prop where
  densityFloor_nonneg : 0 ≤ ρ
  defectThreshold_pos : 0 < β
  defectError_nonneg : 0 ≤ δ
  tolerance_nonneg :
    ∀ j,
      0 ≤ selectedOrderedComplexTolerance ε R.index j
  defectThreshold_le_sq : β ≤ δ ^ 2
  counting_margin :
    c ≤
      (∏ _e : PositiveOrderedFace k r, ρ) -
        (∑ e : PositiveOrderedFace k r,
          (δ +
            selectedOrderedComplexTolerance
              ε R.index e.lowerRank))
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
      FacePartition.complexity
        (R.coarse.partition j.succ e) ≤ coarseBound
  deletion_margin :
    (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (coarseBound : ℝ) * ρ +
        R.toCoarseFine.totalCoarseUpperAtomEnergyGap / β ≤
      ξ

/-! ## Stage-indexed ambient-independent schedules -/

/-- A complete ambient-independent coarse-target removal schedule.

The three cleaning/counting parameters depend on the complete finite selected
index vector.  `countThreshold` is a single positive number that works for
every possible vector, so it is chosen before the ambient type and input
pattern are known. -/
structure StageIndexedCoarseTargetRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  densityFloor : CoarseTargetStageIndex length → ℝ
  defectThreshold : CoarseTargetStageIndex length → ℝ
  defectError : CoarseTargetStageIndex length → ℝ
  countThreshold : ℝ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  densityFloor_nonneg :
    ∀ index, 0 ≤ densityFloor index
  defectThreshold_pos :
    ∀ index, 0 < defectThreshold index
  defectError_nonneg :
    ∀ index, 0 ≤ defectError index
  defectThreshold_le_sq :
    ∀ index,
      defectThreshold index ≤ (defectError index) ^ 2
  countThreshold_pos : 0 < countThreshold
  uniform_counting_margin :
    ∀ index : CoarseTargetStageIndex length,
      countThreshold ≤
        (∏ _e : PositiveOrderedFace k r,
          densityFloor index) -
          (∑ e : PositiveOrderedFace k r,
            (defectError index +
              tolerance e.lowerRank
                (index e.lowerRank).1))
  uniform_deletion_margin :
    ∀ index : CoarseTargetStageIndex length,
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
            (coarseTargetSelectedCoarseComplexityBound
              r initialBound budget length index : ℝ) *
            densityFloor index +
          (∑ j : Fin r,
            (Fintype.card
              (OrderedFace k (j.1 + 1)) : ℝ) /
                (length j : ℝ)) /
            defectThreshold index ≤
        ξ

/-- Existence of a stage-indexed compatible schedule for every positive
removal allowance.  This is the deliberately unproved selector obligation. -/
def HasStageIndexedCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (StageIndexedCoarseTargetRemovalSchedule
        k r initialBound ξ)

/-! ## Certificate-level semantic assembly -/

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- One compatible coarse-target certificate produces a cover whose
per-top-face deletion density is at most `ξ`.  The count threshold `c` is an
explicit parameter and need not be reconstructed from the certificate. -/
theorem removal_of_compatible
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrank : n + 1 ≤ k)
    {initial : OrderedPartitionComplex G k (n + 1)}
    {ε : (j : Fin (n + 1)) → ℕ → ℝ}
    {budget : (j : Fin (n + 1)) → ℕ → ℕ}
    {length : Fin (n + 1) → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k (n + 1) initial ε budget length)
    (H : OrderedPattern G k (n + 1))
    (hinitial :
      R.coarse.Refines (orderedPatternInitialComplex H))
    {ξ c ρ β δ : ℝ} {coarseBound : ℕ}
    (hcompatible :
      IsCoarseTargetRemovalCertificateCompatible
        R ξ c ρ β δ coarseBound)
    (hcount : H.toWeighted.patternCount < c) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k (n + 1),
      H.IsCover D ∧
        ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  let P : OrderedCoarseFineComplex G k (n + 1) :=
    R.toCoarseFine
  let α : ℕ → ℝ := fun _ => ρ
  let βs : ℕ → ℝ := fun _ => β
  let δs : ℕ → ℝ := fun _ => δ
  let τ : OrderedRegularityTolerance (n + 1) :=
    selectedOrderedComplexTolerance ε R.index
  let D : OrderedPattern.DeletionFamily
      (G := G) k (n + 1) :=
    P.orderedCoarseBadBaseDeletionFamily α βs
  have hcount' :
      H.toWeighted.patternCount <
        (∏ e : PositiveOrderedFace k (n + 1),
            α e.rank) -
          (∑ e : PositiveOrderedFace k (n + 1),
            (δs e.rank + τ e.lowerRank)) := by
    apply lt_of_lt_of_le hcount
    simpa [α, δs, τ] using hcompatible.counting_margin
  have hcover : H.IsCover D := by
    apply
      orderedCoarseBadBaseDeletionFamily_isCover_rankwise
        hrank H P hinitial α βs τ
        R.isFullyMixedPreliminaryOrderedRegular
        δs
    · intro m
      exact hcompatible.densityFloor_nonneg
    · intro j
      exact hcompatible.tolerance_nonneg j
    · intro m
      exact hcompatible.defectError_nonneg
    · intro m
      exact hcompatible.defectThreshold_pos.le
    · intro m
      exact hcompatible.defectThreshold_le_sq
    · exact hcount'
  refine ⟨D, hcover, ?_⟩
  intro e
  have hdeletion :=
    P.faceDeletionDensity_orderedCoarseBadBase_constant_coarseTarget_le
      hcompatible.coarse_complexity
      hcompatible.densityFloor_nonneg
      hcompatible.defectThreshold_pos e
  exact hdeletion.trans hcompatible.deletion_margin

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## A schedule supplies compatible certificates -/

namespace StageIndexedCoarseTargetRemovalSchedule

/-- A schedule supplies a coarse-target certificate over every ambient finite
type and initial complex. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : StageIndexedCoarseTargetRemovalSchedule
      k r initialBound ξ)
    (initial : OrderedPartitionComplex G k r) :
    Nonempty
      (CoarseTargetOrderedComplexRegularityCertificate
        G k r initial S.tolerance S.budget S.length) := by
  exact
    CoarseTargetOrderedComplexRegularityCertificate.nonempty
      initial S.tolerance S.budget S.length
      (fun j n => (S.tolerance_pos j n).le)
      S.budget_spec S.length_pos

/-- The vector-indexed schedule inequalities specialize to the actual index
vector selected by any certificate. -/
theorem certificateCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ} {ξ : ℝ}
    {initial : OrderedPartitionComplex G k r}
    (S : StageIndexedCoarseTargetRemovalSchedule
      k r initialBound ξ)
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial S.tolerance S.budget S.length)
    (hinitial :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j e) ≤ initialBound) :
    IsCoarseTargetRemovalCertificateCompatible
      R ξ S.countThreshold
      (S.densityFloor R.stageIndex)
      (S.defectThreshold R.stageIndex)
      (S.defectError R.stageIndex)
      (coarseTargetSelectedCoarseComplexityBound
        r initialBound S.budget S.length R.stageIndex) := by
  let index : CoarseTargetStageIndex S.length :=
    R.stageIndex
  refine {
    densityFloor_nonneg :=
      S.densityFloor_nonneg index
    defectThreshold_pos :=
      S.defectThreshold_pos index
    defectError_nonneg :=
      S.defectError_nonneg index
    tolerance_nonneg := ?_
    defectThreshold_le_sq :=
      S.defectThreshold_le_sq index
    counting_margin := ?_
    coarse_complexity := ?_
    deletion_margin := ?_ }
  · intro j
    exact
      (S.tolerance_pos j (R.index j)).le
  · simpa [index, selectedOrderedComplexTolerance,
      CoarseTargetOrderedComplexRegularityCertificate.stageIndex] using
      S.uniform_counting_margin index
  · intro j e
    exact
      R.coarse_complexity_le_selectedBound hinitial j.succ e
  · have hgap :=
      R.totalCoarseUpperAtomEnergyGap_le_sum_div
    calc
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
              (coarseTargetSelectedCoarseComplexityBound
                r initialBound S.budget S.length R.stageIndex : ℝ) *
              S.densityFloor R.stageIndex +
            R.toCoarseFine.totalCoarseUpperAtomEnergyGap /
              S.defectThreshold R.stageIndex ≤
          (Fintype.card (OrderedPositiveSubface r) : ℝ) *
              (coarseTargetSelectedCoarseComplexityBound
                r initialBound S.budget S.length R.stageIndex : ℝ) *
              S.densityFloor R.stageIndex +
            (∑ j : Fin r,
              (Fintype.card
                (OrderedFace k (j.1 + 1)) : ℝ) /
                  (S.length j : ℝ)) /
              S.defectThreshold R.stageIndex := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_right hgap
            (S.defectThreshold_pos R.stageIndex).le)
      _ ≤ ξ :=
        S.uniform_deletion_margin R.stageIndex

/-- Certificate-level removal specialized directly from a stage-indexed
schedule. -/
theorem certificateRemoval
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n initialBound : ℕ} {ξ : ℝ}
    (hrank : n + 1 ≤ k)
    (S : StageIndexedCoarseTargetRemovalSchedule
      k (n + 1) initialBound ξ)
    (H : OrderedPattern G k (n + 1))
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k (n + 1) (orderedPatternInitialComplex H)
        S.tolerance S.budget S.length)
    (hinitial :
      ∀ (j : Fin (n + 2)) (e : OrderedFace k j.1),
        FacePartition.complexity
          ((orderedPatternInitialComplex H).partition j e) ≤
            initialBound)
    (hcount :
      H.toWeighted.patternCount < S.countThreshold) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k (n + 1),
      H.IsCover D ∧
        ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  exact R.removal_of_compatible
    hrank H R.coarse_refines_initial
    (S.certificateCompatible R hinitial) hcount

end StageIndexedCoarseTargetRemovalSchedule

/-! ## Conditional uniform ordered removal -/

/-- Existence of ambient-independent stage-indexed coarse-target schedules
implies uniform ordered-pattern removal at successor rank.  The schedule
existence hypothesis is the remaining quantified selector obligation. -/
theorem hasUniformOrderedPatternRemoval_succ_of_coarseTargetSchedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasStageIndexedCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  let S : StageIndexedCoarseTargetRemovalSchedule
      k (n + 1) 2 ξ :=
    Classical.choice (hschedules ξ hξ)
  refine ⟨S.countThreshold, S.countThreshold_pos, ?_⟩
  intro G instFintype instDecidableEq instNonempty H hcount
  let initial : OrderedPartitionComplex G k (n + 1) :=
    orderedPatternInitialComplex H
  obtain ⟨R⟩ := S.certificate_nonempty initial
  exact S.certificateRemoval
    hrank H R
    (complexity_orderedPatternInitialComplex_le_two H)
    hcount

end Submission.GreenTao
