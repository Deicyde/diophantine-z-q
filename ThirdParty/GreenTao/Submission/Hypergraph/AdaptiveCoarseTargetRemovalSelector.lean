import Submission.Hypergraph.AdaptiveCoarseTargetRegularity
import Submission.Hypergraph.RankwiseStageShiftedRegularity

/-!
# Adaptive coarse-target removal selectors

An ordinary coarse-target removal schedule fixes a Cartesian product of
tower horizons before regularity selects any index.  The adaptive regularity
theorem instead uses a finite decision tree: after the index at the current
highest rank is selected, that index chooses the complete schedule for all
lower ranks.

This file gives the corresponding numerical removal interface.  Numerical
density and defect data are attached only to genuine root-to-leaf landings.
The count threshold is independent of the landing and of the ambient finite
type.  The main theorem realizes one landing, transports the certificate
indices across the realization equality, and invokes the existing
rankwise-selected removal theorem directly.  No fixed Cartesian horizon
vector is introduced.
-/

namespace Submission.GreenTao

open scoped BigOperators

namespace AdaptiveCoarseTargetSchedule

namespace Landing

/-- The bounded stage vector recorded by a genuine adaptive landing. -/
def stageIndex
    {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    CoarseTargetStageIndex P.length :=
  fun j => ⟨P.index j, P.index_lt_length j⟩

@[simp]
theorem stageIndex_val
    {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing)
    (j : Fin r) :
    (P.stageIndex j).1 = P.index j :=
  rfl

end Landing

end AdaptiveCoarseTargetSchedule

/-- Ambient-independent numerical data on the genuine landings of an
adaptive coarse-target schedule.

Every landing may have its own flattened tolerance, budget, horizon,
density floors, and defect data.  Only `countThreshold` is shared between
landings.  This is precisely the uniformity needed by ordered-pattern
removal: the ambient complex may affect which landing regularity realizes,
but it cannot affect the threshold below which the pattern is removable. -/
structure AdaptiveRankwiseCoarseTargetRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  schedule : AdaptiveCoarseTargetSchedule k r
  schedule_admissible : schedule.IsAdmissible
  densityFloor :
    schedule.Landing → Fin r → ℝ
  defectThreshold :
    schedule.Landing → Fin r → ℝ
  defectError :
    schedule.Landing → Fin r → ℝ
  countThreshold : ℝ
  countThreshold_pos : 0 < countThreshold
  densityFloor_nonneg :
    ∀ P j, 0 ≤ densityFloor P j
  defectThreshold_pos :
    ∀ P j, 0 < defectThreshold P j
  defectError_nonneg :
    ∀ P j, 0 ≤ defectError P j
  defectThreshold_le_sq :
    ∀ P j,
      defectThreshold P j ≤ (defectError P j) ^ 2
  landing_counting_margin :
    ∀ P : schedule.Landing,
      countThreshold ≤
        (∏ e : PositiveOrderedFace k r,
          densityFloor P e.lowerRank) -
          (∑ e : PositiveOrderedFace k r,
            (defectError P e.lowerRank +
              P.tolerance e.lowerRank
                (P.index e.lowerRank)))
  landing_deletion_margin :
    ∀ P : schedule.Landing,
      (∑ q : OrderedPositiveSubface r,
        (((CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
                  r initialBound P.budget P.length
                    P.stageIndex q.1 : ℕ) : ℝ) *
              densityFloor P q.1 +
            ((Fintype.card
                (OrderedFace k (q.1.1 + 1)) : ℝ) /
                  (P.length q.1 : ℝ)) /
              defectThreshold P q.1)) ≤
        ξ

/-- Existence, for every positive removal allowance, of one adaptive
schedule with a landing-uniform positive count threshold. -/
def HasAdaptiveRankwiseCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (AdaptiveRankwiseCoarseTargetRemovalSchedule
        k r initialBound ξ)

namespace AdaptiveRankwiseCoarseTargetRemovalSchedule

/-- The index equality supplied by adaptive regularity also identifies the
certificate's bounded stage vector with the landing's bounded stage vector.
This is the key dependent substitution used by the complexity bound. -/
theorem stageIndex_eq_landing
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing)
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial P.tolerance P.budget P.length)
    (hindex : R.index = P.index) :
    R.stageIndex = P.stageIndex := by
  funext j
  apply Fin.ext
  exact congrFun hindex j

/-- A realized adaptive landing supplies the existing certificate-level
rankwise-selected compatibility package.

The initial-complexity hypothesis is used only to bound the selected coarse
upper layers.  All counting and deletion data come from the realized
landing itself. -/
def selectedCompatibility
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : AdaptiveRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ)
    {initial : OrderedPartitionComplex G k r}
    (P : S.schedule.Landing)
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial P.tolerance P.budget P.length)
    (hindex : R.index = P.index)
    (hinitial :
      ∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound) :
    RankwiseSelectedCoarseTargetCompatibility
      R ξ S.countThreshold where
  upperBound := fun j =>
    CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
      r initialBound P.budget P.length P.stageIndex j
  densityFloor := S.densityFloor P
  defectThreshold := S.defectThreshold P
  defectError := S.defectError P
  densityFloor_nonneg := S.densityFloor_nonneg P
  defectThreshold_pos := S.defectThreshold_pos P
  defectError_nonneg := S.defectError_nonneg P
  tolerance_nonneg := by
    intro j
    rw [selectedOrderedComplexTolerance, congrFun hindex j]
    exact P.tolerance_nonneg S.schedule_admissible j (P.index j)
  defectThreshold_le_sq := S.defectThreshold_le_sq P
  counting_margin := by
    simpa [selectedOrderedComplexTolerance, hindex] using
      S.landing_counting_margin P
  coarse_upper_complexity := by
    intro j e
    have hbound :=
      R.coarse_upper_complexity_le_selectedUpperBound
        hinitial j e
    rw [stageIndex_eq_landing P R hindex] at hbound
    exact hbound
  deletion_margin := S.landing_deletion_margin P

/-- One adaptive numerical schedule gives uniform ordered-pattern removal.

For each ambient pattern, `exists_landing_certificate` follows the actual
top-down decision path.  The landing-specific numerical data are then
compiled into `RankwiseSelectedCoarseTargetCompatibility`, while the single
positive `countThreshold` chosen by the schedule remains unchanged. -/
theorem hasUniformOrderedPatternRemoval_succ
    {k n initialBound : ℕ} {ξ : ℝ}
    (hrank : n + 1 ≤ k)
    (S : AdaptiveRankwiseCoarseTargetRemovalSchedule
      k (n + 1) initialBound ξ)
    (hinitial :
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
        (H : OrderedPattern G k (n + 1))
        (j : Fin (n + 2))
        (e : OrderedFace k j.1),
        FacePartition.complexity
            ((orderedPatternInitialComplex H).partition j e) ≤
          initialBound) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k (n + 1),
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k (n + 1),
              H.IsCover D ∧
                ∀ e,
                  OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  refine ⟨S.countThreshold, S.countThreshold_pos, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  obtain ⟨P, R, hindex⟩ :=
    S.schedule.exists_landing_certificate
      (orderedPatternInitialComplex H)
      S.schedule_admissible
  let C : RankwiseSelectedCoarseTargetCompatibility
      R ξ S.countThreshold :=
    S.selectedCompatibility P R hindex
      (hinitial G H)
  exact
    R.removal_of_rankwiseSelectedCompatibility
      hrank H R.coarse_refines_initial C hcount

end AdaptiveRankwiseCoarseTargetRemovalSchedule

/-- Adaptive landing schedules imply uniform ordered-pattern removal at
successor rank.  The specialization to initial bound `2` uses the canonical
ordered-pattern initial-complexity estimate. -/
theorem hasUniformOrderedPatternRemoval_succ_of_adaptiveSchedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasAdaptiveRankwiseCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  obtain ⟨S⟩ := hschedules ξ hξ
  exact
    S.hasUniformOrderedPatternRemoval_succ hrank
      (fun _G _instFintype _instDecidableEq _instNonempty H =>
        complexity_orderedPatternInitialComplex_le_two H)

end Submission.GreenTao
