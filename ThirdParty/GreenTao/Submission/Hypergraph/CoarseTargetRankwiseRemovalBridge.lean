import Submission.Hypergraph.CoarseTargetRemovalSchedules

/-!
# Rankwise coarse-target cleaning bounds

The constant-parameter bridge in `CoarseTargetRemovalBridge` is convenient,
but it forgets the parameter hierarchy used in the hypergraph removal
argument.  At rank `j + 1`, both the low-density threshold and the localized
defect threshold should be chosen from the complexity of the coarse
`(j + 1)`-layer.  The energy gap which pays for that defect is the gap in the
adjacent `j`-layer.

This file keeps those ranks separate.  In particular, the reciprocal length
at rank `j` is divided only by the defect threshold at rank `j + 1`; no
minimum defect threshold over all ranks is introduced.
-/

namespace Submission.GreenTao

open scoped BigOperators

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Stage-indexed bound for the coarse upper partition at rank `j + 1`.

The top layer is unchanged, so its bound is exactly `initialBound`.  Away
from the top, rank `j + 1` is itself a selected lower layer and is bounded by
its own tower factor.  In particular, the rank-zero tower factor is never
charged to a rank-one top layer. -/
def coarseTargetSelectedUpperComplexityBound
    (r initialBound : ℕ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (index : CoarseTargetStageIndex length)
    (j : Fin r) : ℕ :=
  if h : j.1 + 1 < r then
    initialBound *
      fixedUpperLayerComplexityFactor
        (j.1 + 1) (budget ⟨j.1 + 1, h⟩)
          (index ⟨j.1 + 1, h⟩).1
  else
    initialBound

/-- Every selected coarse upper partition satisfies the adjacent-rank
stage bound. -/
theorem coarse_upper_complexity_le_selectedUpperBound
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
          (initial.partition j e) ≤ initialBound)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.coarse.partition j.succ e) ≤
      coarseTargetSelectedUpperComplexityBound
        r initialBound budget length R.stageIndex j := by
  cases r with
  | zero =>
      exact Fin.elim0 j
  | succ s =>
      cases j using Fin.lastCases with
      | last =>
          simp only [Fin.succ_last] at e ⊢
          have htop := congrFun R.coarse_topLayer_eq e
          simp only [OrderedPartitionComplex.topLayer] at htop
          rw [htop]
          have hnot :
              ¬ (Fin.last s).1 + 1 < s + 1 := by
            simp
          rw [coarseTargetSelectedUpperComplexityBound,
            dif_neg hnot]
          convert hinitial (Fin.last (s + 1)) e using 1
          all_goals rfl
      | cast i =>
          have hcomplexity := R.coarse_complexity i.succ e
          have hinitial' := hinitial i.succ.castSucc e
          calc
            FacePartition.complexity
                (R.coarse.partition i.castSucc.succ e) ≤
                fixedUpperLayerComplexityFactor
                    i.succ.1 (budget i.succ) (R.index i.succ) *
                  FacePartition.complexity
                    (initial.partition i.succ.castSucc e) := by
              convert hcomplexity using 1
              all_goals rfl
            _ ≤
                fixedUpperLayerComplexityFactor
                    i.succ.1 (budget i.succ) (R.index i.succ) *
                  initialBound :=
              Nat.mul_le_mul_left _ hinitial'
            _ =
                coarseTargetSelectedUpperComplexityBound
                  (s + 1) initialBound budget length
                    R.stageIndex i.castSucc := by
              have hi :
                  i.castSucc.1 + 1 < s + 1 := by
                simpa only [Fin.val_castSucc] using
                  Nat.succ_lt_succ i.isLt
              rw [coarseTargetSelectedUpperComplexityBound, dif_pos hi]
              have hq :
                  (⟨i.castSucc.1 + 1, hi⟩ :
                    Fin (s + 1)) = i.succ := by
                apply Fin.ext
                rfl
              rw [hq]
              simp only [stageIndex]
              rw [Nat.mul_comm]
              simp only [Fin.val_succ, Fin.val_castSucc]

/-- The coarse-upper energy gap at one selected rank is bounded by the
corresponding reciprocal tower length. -/
theorem coarseUpperLayerAtomEnergyGap_le_div
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (j : Fin r) :
    R.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (length j : ℝ) := by
  simpa [
    OrderedCoarseFineComplex.coarseUpperLayerAtomEnergyGap,
    toCoarseFine] using R.gap_le j

end CoarseTargetOrderedComplexRegularityCertificate

namespace OrderedCoarseFineComplex

/-- A single coarse-upper face gap is at most the complete gap in its
ordered layer. -/
theorem coarseUpperFaceAtomEnergyGap_le_layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    P.coarseUpperFaceAtomEnergyGap j e ≤
      P.coarseUpperLayerAtomEnergyGap j := by
  rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face j]
  exact Finset.single_le_sum
    (fun f _ => P.coarseUpperFaceAtomEnergyGap_nonneg j f)
    (Finset.mem_univ e)

end OrderedCoarseFineComplex

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Rankwise coarse-target cleaning estimate.

`upperBound j` bounds the coarse partition at rank `j + 1`.  The low-density
loss for a subface of that rank is therefore
`upperBound j * α (j + 1)`.  Its defect loss is paid by the adjacent
rank-`j` coarse-target gap, hence by
`card (OrderedFace k (j + 1)) / length j`, divided by `β (j + 1)`.

The displayed sum intentionally keeps one summand per positive subface.  It
is slightly weaker than first summing the face gaps inside each rank, but it
has a simple ambient-independent form and, crucially, preserves the
rankwise parameter dependency. -/
theorem faceDeletionDensity_orderedCoarseBadBase_rankwise_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (upperBound : Fin r → ℕ)
    (hcoarse :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (R.coarse.partition j.succ e) ≤ upperBound j)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (R.toCoarseFine.orderedCoarseBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((upperBound q.1 : ℝ) * α (q.1.1 + 1) +
          ((Fintype.card
              (OrderedFace k (q.1.1 + 1)) : ℝ) /
                (length q.1 : ℝ)) /
            β (q.1.1 + 1)) := by
  have hbase :=
    R.toCoarseFine.faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
      α β hα hβ e
  refine hbase.trans ?_
  apply Finset.sum_le_sum
  intro q _hq
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (hcoarse q.1 (q.2.trans e)))
      (hα q.1.1)
  · apply div_le_div_of_nonneg_right _ (hβ q.1.1).le
    exact
      (R.toCoarseFine.coarseUpperFaceAtomEnergyGap_le_layer
          q.1 (q.2.trans e)).trans
        (R.coarseUpperLayerAtomEnergyGap_le_div q.1)

end CoarseTargetOrderedComplexRegularityCertificate

end Submission.GreenTao
