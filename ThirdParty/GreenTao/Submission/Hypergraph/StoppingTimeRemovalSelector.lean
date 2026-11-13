import Submission.Hypergraph.RankwiseStageShiftedRegularity

/-!
# Reachable stopping-time paths for ordered removal

The stage vector selected by coarse-target regularity is not an arbitrary
point of the finite stage box: it is realized by an actual regularity
certificate.  This file packages that ambient-independent reachability
predicate and uses it as the admissible-path family in the stopping-time
removal interface.

This construction deliberately makes no claim that every reachable path
satisfies the numerical counting and deletion margins.  Those margins are
the remaining mathematical parameter-selection problem.  The purpose of
the interface below is to state that problem on exactly the paths produced
by regularity, and to prove once and for all that a selected certificate
lands in that set.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-- A bounded rankwise stage vector is reachable when it is the selected
stage vector of an actual coarse-target regularity certificate over some
finite nonempty ambient type and some input complex.

The ambient type is quantified inside the predicate, so the resulting set
of paths depends only on the numerical schedules.  It is the exact union of
all certificate paths, hence the smallest ambient-independent admissible
family which is guaranteed to contain every certificate path. -/
def ReachableCoarseTargetStageIndex
    (k r : ℕ)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (index : CoarseTargetStageIndex length) : Prop :=
  ∃ (G : Type) (fintypeG : Fintype G)
      (decidableEqG : DecidableEq G) (_nonemptyG : Nonempty G)
      (initial :
        @OrderedPartitionComplex
          G fintypeG decidableEqG k r),
    ∃ R :
        @CoarseTargetOrderedComplexRegularityCertificate
          G fintypeG decidableEqG k r initial
            tolerance budget length,
      @CoarseTargetOrderedComplexRegularityCertificate.stageIndex
          G fintypeG decidableEqG k r initial
            tolerance budget length R =
        index

/-- Every certificate's selected stage vector belongs to the
ambient-independent reachable-path family. -/
theorem CoarseTargetOrderedComplexRegularityCertificate.stageIndex_reachable
    {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length) :
    ReachableCoarseTargetStageIndex
      k r tolerance budget length R.stageIndex := by
  exact ⟨G, inferInstance, inferInstance, inferInstance,
    initial, R, rfl⟩

/-- Reachability is the least ambient-independent path predicate containing
the selected path of every certificate. -/
theorem ReachableCoarseTargetStageIndex.mono_of_stageIndex
    {k r : ℕ}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (admissible : CoarseTargetStageIndex length → Prop)
    (hcertificate :
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
        (initial : OrderedPartitionComplex G k r)
        (R : CoarseTargetOrderedComplexRegularityCertificate
          G k r initial tolerance budget length),
        admissible R.stageIndex)
    {index : CoarseTargetStageIndex length}
    (hindex :
      ReachableCoarseTargetStageIndex
        k r tolerance budget length index) :
    admissible index := by
  obtain ⟨G, fintypeG, decidableEqG, nonemptyG,
      initial, R, rfl⟩ := hindex
  letI : Fintype G := fintypeG
  letI : DecidableEq G := decidableEqG
  letI : Nonempty G := nonemptyG
  exact hcertificate G initial R

/-- Under the hypotheses of coarse-target regularity, every input complex
admits a certificate whose selected path is reachable. -/
theorem exists_coarseTargetCertificate_with_reachable_stageIndex
    {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 ≤ tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    ∃ R : CoarseTargetOrderedComplexRegularityCertificate
        G k r initial tolerance budget length,
      ReachableCoarseTargetStageIndex
        k r tolerance budget length R.stageIndex := by
  obtain ⟨R⟩ :=
    CoarseTargetOrderedComplexRegularityCertificate.nonempty
      initial tolerance budget length
        htolerance hbudget hlength
  exact ⟨R, R.stageIndex_reachable⟩

/-! ## The paths of one fixed certificate selector -/

/-- Fix the certificate returned by the coarse-target existence theorem.
Making this choice explicit is essential: the bare certificate structure
does not remember which energy-pigeonhole witness produced its index. -/
noncomputable def chosenCoarseTargetOrderedComplexRegularityCertificate
    {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 ≤ tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length :=
  Classical.choice
    (CoarseTargetOrderedComplexRegularityCertificate.nonempty
      initial tolerance budget length
        htolerance hbudget hlength)

/-- A bounded stage vector is selected when it is the path of the fixed
coarse-target certificate selector for some finite nonempty ambient type
and some input complex.

Unlike `ReachableCoarseTargetStageIndex`, this predicate does not range over
all structures satisfying the certificate fields.  It records exactly one
energy-pigeonhole choice for each input. -/
def SelectedCoarseTargetStageIndex
    (k r : ℕ)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 ≤ tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j)
    (index : CoarseTargetStageIndex length) : Prop :=
  ∃ (G : Type) (fintypeG : Fintype G)
      (decidableEqG : DecidableEq G) (nonemptyG : Nonempty G)
      (initial :
        @OrderedPartitionComplex
          G fintypeG decidableEqG k r),
    @CoarseTargetOrderedComplexRegularityCertificate.stageIndex
        G fintypeG decidableEqG k r initial
          tolerance budget length
          (@chosenCoarseTargetOrderedComplexRegularityCertificate
            G fintypeG decidableEqG nonemptyG k r initial
              tolerance budget length
              htolerance hbudget hlength) =
      index

/-- The fixed selector's certificate path belongs to the selected-path
family by construction. -/
theorem chosenCoarseTargetOrderedComplexRegularityCertificate.stageIndex_selected
    {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 ≤ tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    SelectedCoarseTargetStageIndex
      k r tolerance budget length
        htolerance hbudget hlength
        (chosenCoarseTargetOrderedComplexRegularityCertificate
          initial tolerance budget length
            htolerance hbudget hlength).stageIndex := by
  exact ⟨G, inferInstance, inferInstance, inferInstance,
    initial, rfl⟩

/-- Every path of the fixed selector is in particular realized by an
actual coarse-target certificate. -/
theorem SelectedCoarseTargetStageIndex.reachable
    {k r : ℕ}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    {htolerance : ∀ j n, 0 ≤ tolerance j n}
    {hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2}
    {hlength : ∀ j, 0 < length j}
    {index : CoarseTargetStageIndex length}
    (hindex :
      SelectedCoarseTargetStageIndex
        k r tolerance budget length
          htolerance hbudget hlength index) :
    ReachableCoarseTargetStageIndex
      k r tolerance budget length index := by
  obtain ⟨G, fintypeG, decidableEqG, nonemptyG,
      initial, rfl⟩ := hindex
  letI : Fintype G := fintypeG
  letI : DecidableEq G := decidableEqG
  letI : Nonempty G := nonemptyG
  exact
    (chosenCoarseTargetOrderedComplexRegularityCertificate
      initial tolerance budget length
        htolerance hbudget hlength).stageIndex_reachable

/-- The selected-path predicate relevant to removal also records that the
input complex satisfies the prescribed initial complexity bound.  This is
strictly aligned with `CorrelatedRankwiseCoarseTargetRemovalSelector.select`,
whose input includes exactly that hypothesis. -/
def BoundedSelectedCoarseTargetStageIndex
    (k r initialBound : ℕ)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 ≤ tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j)
    (index : CoarseTargetStageIndex length) : Prop :=
  ∃ (G : Type) (fintypeG : Fintype G)
      (decidableEqG : DecidableEq G) (nonemptyG : Nonempty G)
      (initial :
        @OrderedPartitionComplex
          G fintypeG decidableEqG k r),
    (∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (initial.partition q e) ≤
        initialBound) ∧
    @CoarseTargetOrderedComplexRegularityCertificate.stageIndex
        G fintypeG decidableEqG k r initial
          tolerance budget length
          (@chosenCoarseTargetOrderedComplexRegularityCertificate
            G fintypeG decidableEqG nonemptyG k r initial
              tolerance budget length
              htolerance hbudget hlength) =
      index

/-- A bounded input's chosen certificate lands in the bounded selected-path
family. -/
theorem chosenCoarseTargetOrderedComplexRegularityCertificate.stageIndex_boundedSelected
    {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (tolerance : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (htolerance : ∀ j n, 0 ≤ tolerance j n)
    (hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2)
    (hlength : ∀ j, 0 < length j)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound) :
    BoundedSelectedCoarseTargetStageIndex
      k r initialBound tolerance budget length
        htolerance hbudget hlength
        (chosenCoarseTargetOrderedComplexRegularityCertificate
          initial tolerance budget length
            htolerance hbudget hlength).stageIndex := by
  exact ⟨G, inferInstance, inferInstance, inferInstance,
    initial, hinitial, rfl⟩

/-- Forgetting the input complexity witness sends bounded selected paths to
selected paths. -/
theorem BoundedSelectedCoarseTargetStageIndex.selected
    {k r initialBound : ℕ}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    {htolerance : ∀ j n, 0 ≤ tolerance j n}
    {hbudget :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (tolerance j n) ^ 2}
    {hlength : ∀ j, 0 < length j}
    {index : CoarseTargetStageIndex length}
    (hindex :
      BoundedSelectedCoarseTargetStageIndex
        k r initialBound tolerance budget length
          htolerance hbudget hlength index) :
    SelectedCoarseTargetStageIndex
      k r tolerance budget length
        htolerance hbudget hlength index := by
  obtain ⟨G, fintypeG, decidableEqG, nonemptyG,
      initial, _hinitial, hstage⟩ := hindex
  exact ⟨G, fintypeG, decidableEqG, nonemptyG,
    initial, hstage⟩

/-! ## Numerical schedules on exactly the reachable paths -/

/-- Rankwise counting and cleaning data required only on stage vectors
which are realized by an actual coarse-target regularity certificate.

Compared with `StoppingTimeRankwiseCoarseTargetRemovalSchedule`, this
structure does not ask the caller to invent an admissibility predicate or
prove a separate landing theorem.  Its admissible set is canonically the
reachable-path family above. -/
structure ReachablePathRankwiseCoarseTargetRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  densityFloor :
    CoarseTargetStageIndex length → Fin r → ℝ
  defectThreshold :
    CoarseTargetStageIndex length → Fin r → ℝ
  defectError :
    CoarseTargetStageIndex length → Fin r → ℝ
  countThreshold : ℝ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  densityFloor_nonneg :
    ∀ index,
      ReachableCoarseTargetStageIndex
          k r tolerance budget length index →
        ∀ j, 0 ≤ densityFloor index j
  defectThreshold_pos :
    ∀ index,
      ReachableCoarseTargetStageIndex
          k r tolerance budget length index →
        ∀ j, 0 < defectThreshold index j
  defectError_nonneg :
    ∀ index,
      ReachableCoarseTargetStageIndex
          k r tolerance budget length index →
        ∀ j, 0 ≤ defectError index j
  defectThreshold_le_sq :
    ∀ index,
      ReachableCoarseTargetStageIndex
          k r tolerance budget length index →
        ∀ j,
          defectThreshold index j ≤
            (defectError index j) ^ 2
  countThreshold_pos : 0 < countThreshold
  reachable_counting_margin :
    ∀ index : CoarseTargetStageIndex length,
      ReachableCoarseTargetStageIndex
          k r tolerance budget length index →
        countThreshold ≤
          (∏ e : PositiveOrderedFace k r,
            densityFloor index e.lowerRank) -
            (∑ e : PositiveOrderedFace k r,
              (defectError index e.lowerRank +
                tolerance e.lowerRank
                  (index e.lowerRank).1))
  reachable_deletion_margin :
    ∀ index : CoarseTargetStageIndex length,
      ReachableCoarseTargetStageIndex
          k r tolerance budget length index →
        (∑ q : OrderedPositiveSubface r,
          (((CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
                    r initialBound budget length
                      index q.1 : ℕ) : ℝ) *
                densityFloor index q.1 +
              ((Fintype.card
                  (OrderedFace k (q.1.1 + 1)) : ℝ) /
                    (length q.1 : ℝ)) /
                defectThreshold index q.1)) ≤
          ξ

/-- Reachable-path numerical data canonically produces the existing
stopping-time schedule.  The regularity existence theorem supplies a
certificate, and `stageIndex_reachable` supplies its admissibility proof. -/
def ReachablePathRankwiseCoarseTargetRemovalSchedule.toStoppingTimeSchedule
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : ReachablePathRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ) :
    StoppingTimeRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ where
  tolerance := S.tolerance
  budget := S.budget
  length := S.length
  admissible :=
    ReachableCoarseTargetStageIndex
      k r S.tolerance S.budget S.length
  densityFloor := S.densityFloor
  defectThreshold := S.defectThreshold
  defectError := S.defectError
  countThreshold := S.countThreshold
  tolerance_pos := S.tolerance_pos
  budget_spec := S.budget_spec
  length_pos := S.length_pos
  certificate_admissible := by
    intro G _instFintype _instDecidableEq _instNonempty
      initial
    exact
      exists_coarseTargetCertificate_with_reachable_stageIndex
        initial S.tolerance S.budget S.length
          (fun j n => (S.tolerance_pos j n).le)
          S.budget_spec S.length_pos
  densityFloor_nonneg := S.densityFloor_nonneg
  defectThreshold_pos := S.defectThreshold_pos
  defectError_nonneg := S.defectError_nonneg
  defectThreshold_le_sq := S.defectThreshold_le_sq
  countThreshold_pos := S.countThreshold_pos
  uniform_counting_margin := S.reachable_counting_margin
  uniform_deletion_margin := S.reachable_deletion_margin

/-- Existence of reachable-path numerical schedules at every positive
removal allowance. -/
def HasReachablePathRankwiseCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (ReachablePathRankwiseCoarseTargetRemovalSchedule
        k r initialBound ξ)

/-- Reachable-path schedules discharge the admissible-path schedule
interface without any additional selector hypothesis. -/
theorem hasStoppingTimeSchedules_of_reachablePathSchedules
    (k r initialBound : ℕ)
    (hschedules :
      HasReachablePathRankwiseCoarseTargetRemovalSchedules
        k r initialBound) :
    HasStoppingTimeRankwiseCoarseTargetRemovalSchedules
      k r initialBound := by
  intro ξ hξ
  obtain ⟨S⟩ := hschedules ξ hξ
  exact ⟨S.toStoppingTimeSchedule⟩

/-- The dense semantic endpoint for reachable-path numerical schedules. -/
theorem hasUniformOrderedPatternRemoval_succ_of_reachablePathSchedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasReachablePathRankwiseCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  exact
    hasUniformOrderedPatternRemoval_succ_of_stoppingTimeSchedules
      k n hrank
        (hasStoppingTimeSchedules_of_reachablePathSchedules
          k (n + 1) 2 hschedules)

/-! ## Numerical schedules on the fixed selector's paths -/

/-- The sharp stopping-time parameter interface: numerical margins are
required only on paths returned by the fixed coarse-target certificate
selector. -/
structure SelectedPathRankwiseCoarseTargetRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  densityFloor :
    CoarseTargetStageIndex length → Fin r → ℝ
  defectThreshold :
    CoarseTargetStageIndex length → Fin r → ℝ
  defectError :
    CoarseTargetStageIndex length → Fin r → ℝ
  countThreshold : ℝ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  densityFloor_nonneg :
    ∀ index,
      SelectedCoarseTargetStageIndex
          k r tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j, 0 ≤ densityFloor index j
  defectThreshold_pos :
    ∀ index,
      SelectedCoarseTargetStageIndex
          k r tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j, 0 < defectThreshold index j
  defectError_nonneg :
    ∀ index,
      SelectedCoarseTargetStageIndex
          k r tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j, 0 ≤ defectError index j
  defectThreshold_le_sq :
    ∀ index,
      SelectedCoarseTargetStageIndex
          k r tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j,
          defectThreshold index j ≤
            (defectError index j) ^ 2
  countThreshold_pos : 0 < countThreshold
  selected_counting_margin :
    ∀ index : CoarseTargetStageIndex length,
      SelectedCoarseTargetStageIndex
          k r tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        countThreshold ≤
          (∏ e : PositiveOrderedFace k r,
            densityFloor index e.lowerRank) -
            (∑ e : PositiveOrderedFace k r,
              (defectError index e.lowerRank +
                tolerance e.lowerRank
                  (index e.lowerRank).1))
  selected_deletion_margin :
    ∀ index : CoarseTargetStageIndex length,
      SelectedCoarseTargetStageIndex
          k r tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        (∑ q : OrderedPositiveSubface r,
          (((CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
                    r initialBound budget length
                      index q.1 : ℕ) : ℝ) *
                densityFloor index q.1 +
              ((Fintype.card
                  (OrderedFace k (q.1.1 + 1)) : ℝ) /
                    (length q.1 : ℝ)) /
                defectThreshold index q.1)) ≤
          ξ

/-- Selected-path numerical data is a stopping-time removal schedule.  Its
certificate selector is the fixed choice above, so the admissible-path
landing field is immediate and does not quantify over arbitrary
certificate structures. -/
noncomputable def SelectedPathRankwiseCoarseTargetRemovalSchedule.toStoppingTimeSchedule
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : SelectedPathRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ) :
    StoppingTimeRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ where
  tolerance := S.tolerance
  budget := S.budget
  length := S.length
  admissible :=
    SelectedCoarseTargetStageIndex
      k r S.tolerance S.budget S.length
        (fun j n => (S.tolerance_pos j n).le)
        S.budget_spec S.length_pos
  densityFloor := S.densityFloor
  defectThreshold := S.defectThreshold
  defectError := S.defectError
  countThreshold := S.countThreshold
  tolerance_pos := S.tolerance_pos
  budget_spec := S.budget_spec
  length_pos := S.length_pos
  certificate_admissible := by
    intro G _instFintype _instDecidableEq _instNonempty
      initial
    let R :=
      chosenCoarseTargetOrderedComplexRegularityCertificate
        initial S.tolerance S.budget S.length
          (fun j n => (S.tolerance_pos j n).le)
          S.budget_spec S.length_pos
    exact
      ⟨R,
        chosenCoarseTargetOrderedComplexRegularityCertificate.stageIndex_selected
          initial S.tolerance S.budget S.length
            (fun j n => (S.tolerance_pos j n).le)
            S.budget_spec S.length_pos⟩
  densityFloor_nonneg := S.densityFloor_nonneg
  defectThreshold_pos := S.defectThreshold_pos
  defectError_nonneg := S.defectError_nonneg
  defectThreshold_le_sq := S.defectThreshold_le_sq
  countThreshold_pos := S.countThreshold_pos
  uniform_counting_margin := S.selected_counting_margin
  uniform_deletion_margin := S.selected_deletion_margin

/-- Existence of selected-path numerical schedules at every positive
removal allowance. -/
def HasSelectedPathRankwiseCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (SelectedPathRankwiseCoarseTargetRemovalSchedule
        k r initialBound ξ)

/-- Fixed-selector path schedules discharge the existing stopping-time
schedule interface. -/
theorem hasStoppingTimeSchedules_of_selectedPathSchedules
    (k r initialBound : ℕ)
    (hschedules :
      HasSelectedPathRankwiseCoarseTargetRemovalSchedules
        k r initialBound) :
    HasStoppingTimeRankwiseCoarseTargetRemovalSchedules
      k r initialBound := by
  intro ξ hξ
  obtain ⟨S⟩ := hschedules ξ hξ
  exact ⟨S.toStoppingTimeSchedule⟩

/-- Uniform ordered-pattern removal follows once the numerical margins
are proved on the paths of the fixed coarse-target selector. -/
theorem hasUniformOrderedPatternRemoval_succ_of_selectedPathSchedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasSelectedPathRankwiseCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  exact
    hasUniformOrderedPatternRemoval_succ_of_stoppingTimeSchedules
      k n hrank
        (hasStoppingTimeSchedules_of_selectedPathSchedules
          k (n + 1) 2 hschedules)

/-! ## The bounded-input selected-path interface -/

/-- Numerical removal data only on selected paths arising from inputs of
complexity at most `initialBound`.  This is the narrowest path family used
by the final correlated selector. -/
structure BoundedSelectedPathRankwiseCoarseTargetRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  densityFloor :
    CoarseTargetStageIndex length → Fin r → ℝ
  defectThreshold :
    CoarseTargetStageIndex length → Fin r → ℝ
  defectError :
    CoarseTargetStageIndex length → Fin r → ℝ
  countThreshold : ℝ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  densityFloor_nonneg :
    ∀ index,
      BoundedSelectedCoarseTargetStageIndex
          k r initialBound tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j, 0 ≤ densityFloor index j
  defectThreshold_pos :
    ∀ index,
      BoundedSelectedCoarseTargetStageIndex
          k r initialBound tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j, 0 < defectThreshold index j
  defectError_nonneg :
    ∀ index,
      BoundedSelectedCoarseTargetStageIndex
          k r initialBound tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j, 0 ≤ defectError index j
  defectThreshold_le_sq :
    ∀ index,
      BoundedSelectedCoarseTargetStageIndex
          k r initialBound tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        ∀ j,
          defectThreshold index j ≤
            (defectError index j) ^ 2
  countThreshold_pos : 0 < countThreshold
  selected_counting_margin :
    ∀ index : CoarseTargetStageIndex length,
      BoundedSelectedCoarseTargetStageIndex
          k r initialBound tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        countThreshold ≤
          (∏ e : PositiveOrderedFace k r,
            densityFloor index e.lowerRank) -
            (∑ e : PositiveOrderedFace k r,
              (defectError index e.lowerRank +
                tolerance e.lowerRank
                  (index e.lowerRank).1))
  selected_deletion_margin :
    ∀ index : CoarseTargetStageIndex length,
      BoundedSelectedCoarseTargetStageIndex
          k r initialBound tolerance budget length
            (fun j n => (tolerance_pos j n).le)
            budget_spec length_pos index →
        (∑ q : OrderedPositiveSubface r,
          (((CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
                    r initialBound budget length
                      index q.1 : ℕ) : ℝ) *
                densityFloor index q.1 +
              ((Fintype.card
                  (OrderedFace k (q.1.1 + 1)) : ℝ) /
                    (length q.1 : ℝ)) /
                defectThreshold index q.1)) ≤
          ξ

/-- Bounded selected-path margins produce the certificate-correlated
selector directly.  This avoids enlarging admissibility to paths coming
from input complexes outside the complexity bound used by removal. -/
noncomputable def BoundedSelectedPathRankwiseCoarseTargetRemovalSchedule.toCorrelatedSelector
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : BoundedSelectedPathRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ) :
    CorrelatedRankwiseCoarseTargetRemovalSelector
      k r initialBound ξ where
  tolerance := S.tolerance
  budget := S.budget
  length := S.length
  countThreshold := S.countThreshold
  countThreshold_pos := S.countThreshold_pos
  select := by
    intro G _instFintype _instDecidableEq _instNonempty
      initial hinitial
    let R :=
      chosenCoarseTargetOrderedComplexRegularityCertificate
        initial S.tolerance S.budget S.length
          (fun j n => (S.tolerance_pos j n).le)
          S.budget_spec S.length_pos
    have hselected :
        BoundedSelectedCoarseTargetStageIndex
          k r initialBound S.tolerance S.budget S.length
            (fun j n => (S.tolerance_pos j n).le)
            S.budget_spec S.length_pos R.stageIndex := by
      exact
        chosenCoarseTargetOrderedComplexRegularityCertificate.stageIndex_boundedSelected
          initial S.tolerance S.budget S.length
            (fun j n => (S.tolerance_pos j n).le)
            S.budget_spec S.length_pos hinitial
    refine ⟨R, ⟨{
      upperBound := fun j =>
        CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
          r initialBound S.budget S.length
            R.stageIndex j
      densityFloor :=
        S.densityFloor R.stageIndex
      defectThreshold :=
        S.defectThreshold R.stageIndex
      defectError :=
        S.defectError R.stageIndex
      densityFloor_nonneg := ?_
      defectThreshold_pos := ?_
      defectError_nonneg := ?_
      tolerance_nonneg := ?_
      defectThreshold_le_sq := ?_
      counting_margin := ?_
      coarse_upper_complexity := ?_
      deletion_margin := ?_ }⟩⟩
    · exact S.densityFloor_nonneg R.stageIndex hselected
    · exact S.defectThreshold_pos R.stageIndex hselected
    · exact S.defectError_nonneg R.stageIndex hselected
    · intro j
      exact (S.tolerance_pos j (R.index j)).le
    · exact S.defectThreshold_le_sq R.stageIndex hselected
    · simpa [
        CoarseTargetOrderedComplexRegularityCertificate.stageIndex,
        selectedOrderedComplexTolerance] using
        S.selected_counting_margin R.stageIndex hselected
    · intro j e
      exact
        R.coarse_upper_complexity_le_selectedUpperBound
          hinitial j e
    · exact S.selected_deletion_margin R.stageIndex hselected

/-- Existence of bounded selected-path schedules at every positive removal
allowance. -/
def HasBoundedSelectedPathRankwiseCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (BoundedSelectedPathRankwiseCoarseTargetRemovalSchedule
        k r initialBound ξ)

/-- Bounded selected-path schedules provide the abstract correlated
selectors required by removal. -/
theorem hasCorrelatedSelectors_of_boundedSelectedPathSchedules
    (k r initialBound : ℕ)
    (hschedules :
      HasBoundedSelectedPathRankwiseCoarseTargetRemovalSchedules
        k r initialBound) :
    HasCorrelatedRankwiseCoarseTargetRemovalSelectors
      k r initialBound := by
  intro ξ hξ
  obtain ⟨S⟩ := hschedules ξ hξ
  exact ⟨S.toCorrelatedSelector⟩

/-- Strongest dense endpoint in this file: it is enough to prove the
numerical margins on canonical selected paths of bounded initial
complexes. -/
theorem hasUniformOrderedPatternRemoval_succ_of_boundedSelectedPathSchedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasBoundedSelectedPathRankwiseCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  exact
    hasUniformOrderedPatternRemoval_succ_of_correlatedSelectors
      k n hrank
        (hasCorrelatedSelectors_of_boundedSelectedPathSchedules
          k (n + 1) 2 hschedules)

end Submission.GreenTao
