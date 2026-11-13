-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.HierarchicalParameterSelection
import Submission.Hypergraph.OrderedRemovalAssembly
import Submission.Hypergraph.CoarseTargetRemovalSchedules
import Submission.Hypergraph.CoarseTargetRankwiseRemovalBridge
import Submission.Hypergraph.CoarseTargetRemovalScheduleBase

/-!
# Rankwise stage-shifted regularity windows

The finite-window parameter theorem asks for one bound containing

* every selected lower coarse complexity;
* every adjacent fine-upper complexity; and
* every adjacent coarse-upper complexity.

The regularity certificate already supplies enough information to compute
such a bound *before the energy-pigeonhole indices are selected*.  At rank
`j` the selected index is strictly below
`growthRegularityLength k j (γ j)`.  Monotonicity of the triangular
complexity sequence therefore bounds both selected stages by the terminal
stage at that length.

This file packages those terminal stages into an a priori layer window and
proves that every certificate produced by
`GrowthFunctionOrderedComplexRegularityCertificate.nonempty` lies in it.
The construction is stage-shifted in the important sense that the
complexity used above rank `j` is the independently precomputed bound at
rank `j + 1`, not the fine complexity generated at rank `j`.

The last section isolates the remaining synchronization problem.  The
window is preselected relative to `F` and `γ`, but
`HierarchicalParameterSelection` requires `F = flooredGrowth Q`,
`γ = hierarchicalCommonGap ... B Q ξ`, and the strict inequality

```
growthFunctionAPrioriWindow (... Q ... B ...) ≤ B < Q.
```

The present triangular recurrence computes a regularity budget from
`1 / Q` and then multiplies complexity by an exponential in that budget.
No existing theorem proves this self-bounding inequality.  All other
finite-window hypotheses are discharged below.
-/

namespace Submission.GreenTao

/-! ## A priori layer and common windows -/

/-- Terminal triangular fine-complexity bound at every layer.  At the top
layer no regularity step is performed, so the original top bound is kept.
At a non-top layer `j`, the bound is evaluated at the full
energy-pigeonhole length rather than at the subsequently selected index. -/
noncomputable def growthFunctionAPrioriFineLayerBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      growthRegularityComplexity
        k j.1 (initialBound j.castSucc) F
        (growthRegularityLength k j.1 (γ j)))

/-- One common natural bound containing all a priori layer bounds. -/
noncomputable def growthFunctionAPrioriWindow
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ) : ℕ :=
  finiteMaximum (r + 1)
    (growthFunctionAPrioriFineLayerBound
      k r initialBound F γ)

theorem growthFunctionAPrioriFineLayerBound_le_window
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ)
    (q : Fin (r + 1)) :
    growthFunctionAPrioriFineLayerBound
        k r initialBound F γ q ≤
      growthFunctionAPrioriWindow
        k r initialBound F γ := by
  exact le_finiteMaximum _ q

/-! ## Size of one triangular step -/

/-- An ordered face of rank `s` exists whenever `s ≤ k`. -/
theorem card_orderedFace_pos_of_le
    {k s : ℕ} (hs : s ≤ k) :
    0 < Fintype.card (OrderedFace k s) := by
  exact Fintype.card_pos_iff.mpr
    ⟨Fin.castLEOrderEmb hs⟩

/-- As soon as the relevant ordered-face family is nonempty, the
preliminary-regularity budget is already strictly larger than the growth
value that defines its reciprocal tolerance. -/
theorem growthValue_lt_growthRegularityBudget
    {k j initialBound : ℕ}
    (F : NatGrowthFunction) (n : ℕ)
    (hface :
      0 < Fintype.card (OrderedFace k (j + 1))) :
    F (growthRegularityComplexity
          k j initialBound F n) <
      growthRegularityBudget
        k j initialBound F n := by
  let M :=
    growthRegularityComplexity
      k j initialBound F n
  let q := F M
  let b :=
    growthRegularityBudget
      k j initialBound F n
  have hqNat : 0 < q := F.positive M
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hqNat
  have honeqNat : 1 ≤ q := F.one_le M
  have honeq : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast honeqNat
  have hcard :
      (1 : ℝ) ≤
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) := by
    exact_mod_cast hface
  have hspec :=
    growthRegularityBudget_spec
      k j initialBound F n
  have hspec' :
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
        (b : ℝ) / (q : ℝ) ^ 2 := by
    simpa [b, q, M, one_div_pow,
      div_eq_mul_inv] using hspec
  have hmul :
      (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) *
          (q : ℝ) ^ 2 <
        (b : ℝ) :=
    (lt_div_iff₀ (sq_pos_of_pos hq)).mp hspec'
  have hqSqLe :
      (q : ℝ) ^ 2 ≤
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) *
          (q : ℝ) ^ 2 := by
    simpa using
      (mul_le_mul_of_nonneg_right
        hcard (sq_nonneg (q : ℝ)))
  have hqLeSq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith
  have hreal : (q : ℝ) < (b : ℝ) :=
    hqLeSq.trans_lt (hqSqLe.trans_lt hmul)
  exact_mod_cast hreal

/-- The elementary bound `m ≤ 2^m`. -/
theorem self_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m
  | 0 => by norm_num
  | m + 1 => by
      rw [pow_succ]
      have hpos : 0 < 2 ^ m :=
        pow_pos (by norm_num) _
      have hone : 1 ≤ 2 ^ m := hpos
      have hm := self_le_two_pow m
      omega

/-- With initial complexity `2`, the first triangular step for a floored
growth function already strictly exceeds its floor. -/
theorem flooredGrowth_lt_growthRegularityComplexity_one
    {k j Q : ℕ}
    (hface :
      0 < Fintype.card (OrderedFace k (j + 1))) :
    Q <
      growthRegularityComplexity
        k j 2 (flooredGrowth Q) 1 := by
  let b :=
    growthRegularityBudget
      k j 2 (flooredGrowth Q) 0
  have hQgrowth :
      Q ≤ flooredGrowth Q
        (growthRegularityComplexity
          k j 2 (flooredGrowth Q) 0) := by
    simp [flooredGrowth]
  have hgrowthBudget :
      flooredGrowth Q
          (growthRegularityComplexity
            k j 2 (flooredGrowth Q) 0) <
        b := by
    exact growthValue_lt_growthRegularityBudget
      (flooredGrowth Q) 0 hface
  have hQb : Q < b :=
    hQgrowth.trans_lt hgrowthBudget
  have hbase : 2 ≤ 2 ^ (j + 1) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) :=
        Nat.pow_le_pow_right (by norm_num)
          (by omega)
  have hpow :
      2 ^ b ≤ (2 ^ (j + 1)) ^ b :=
    Nat.pow_le_pow_left hbase b
  have hfactor :
      b ≤ (2 ^ (j + 1)) ^ b :=
    (self_le_two_pow b).trans hpow
  rw [show (1 : ℕ) = 0 + 1 by omega,
    growthRegularityComplexity_succ]
  change Q < (2 ^ (j + 1)) ^ b * 2
  exact hQb.trans_le
    (hfactor.trans
      (Nat.le_mul_of_pos_right _
        (by norm_num)))

/-- At positive rank, the common a priori window for a floored growth
function is strictly larger than the floor itself.  The obstruction is
already visible at the highest non-top rank and at its first regularity
step. -/
theorem flooredGrowth_lt_growthFunctionAPrioriWindow
    (k n Q : ℕ) (hrk : n + 1 ≤ k)
    (γ : Fin (n + 1) → ℝ) :
    Q <
      growthFunctionAPrioriWindow
        k (n + 1) (fun _ => 2)
        (flooredGrowth Q) γ := by
  have hface :
      0 <
        Fintype.card
          (OrderedFace k (n + 1)) :=
    card_orderedFace_pos_of_le hrk
  have hfirst :
      Q <
        growthRegularityComplexity
          k n 2 (flooredGrowth Q) 1 :=
    flooredGrowth_lt_growthRegularityComplexity_one
      hface
  have hlength :
      1 ≤
        growthRegularityLength
          k n (γ (Fin.last n)) :=
    growthRegularityLength_pos
      k n (γ (Fin.last n))
  calc
    Q <
        growthRegularityComplexity
          k n 2 (flooredGrowth Q) 1 :=
      hfirst
    _ ≤
        growthRegularityComplexity
          k n 2 (flooredGrowth Q)
            (growthRegularityLength
              k n (γ (Fin.last n))) :=
      growthRegularityComplexity_monotone
        k n 2 (flooredGrowth Q) hlength
    _ =
        growthFunctionAPrioriFineLayerBound
          k (n + 1) (fun _ => 2)
          (flooredGrowth Q) γ
          (Fin.last n).castSucc := by
      simp [growthFunctionAPrioriFineLayerBound]
    _ ≤
        growthFunctionAPrioriWindow
          k (n + 1) (fun _ => 2)
          (flooredGrowth Q) γ :=
      growthFunctionAPrioriFineLayerBound_le_window
        k (n + 1) (fun _ => 2)
        (flooredGrowth Q) γ
        (Fin.last n).castSucc

/-- Consequently no window strictly below the floor can contain this
triangular a priori bound. -/
theorem not_growthFunctionAPrioriWindow_le_of_bound_lt_floor
    (k n complexityBound Q : ℕ)
    (hrk : n + 1 ≤ k)
    (hQ : complexityBound < Q)
    (γ : Fin (n + 1) → ℝ) :
    ¬
      growthFunctionAPrioriWindow
          k (n + 1) (fun _ => 2)
          (flooredGrowth Q) γ ≤
        complexityBound := by
  intro hwindow
  have hfloor :=
    flooredGrowth_lt_growthFunctionAPrioriWindow
      k n Q hrk γ
  omega

/-! ## Every selected layer lies in the a priori window -/

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- The selected fine numerical layer bound lies below the terminal
triangular bound computed before index selection. -/
theorem selectedFineLayerComplexityBound_le_aPriori
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (q : Fin (r + 1)) :
    selectedGrowthFineLayerComplexityBound
        k r initialBound F R.index q ≤
      growthFunctionAPrioriFineLayerBound
        k r initialBound F γ q := by
  cases q using Fin.lastCases with
  | last =>
      simp [selectedGrowthFineLayerComplexityBound,
        growthFunctionAPrioriFineLayerBound]
  | cast j =>
      simp only [selectedGrowthFineLayerComplexityBound,
        selectedGrowthFineComplexityBound,
        growthFunctionAPrioriFineLayerBound,
        Fin.lastCases_castSucc]
      exact growthRegularityComplexity_monotone
        k j.1 (initialBound j.castSucc) F
        (R.index_lt j)

/-- The selected coarse numerical layer bound lies below the same terminal
fine bound. -/
theorem selectedCoarseLayerComplexityBound_le_aPriori
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (q : Fin (r + 1)) :
    selectedGrowthCoarseLayerComplexityBound
        k r initialBound F R.index q ≤
      growthFunctionAPrioriFineLayerBound
        k r initialBound F γ q := by
  cases q using Fin.lastCases with
  | last =>
      simp [selectedGrowthCoarseLayerComplexityBound,
        growthFunctionAPrioriFineLayerBound]
  | cast j =>
      simp only [selectedGrowthCoarseLayerComplexityBound,
        selectedGrowthCoarseComplexityBound,
        growthFunctionAPrioriFineLayerBound,
        Fin.lastCases_castSucc]
      exact growthRegularityComplexity_monotone
        k j.1 (initialBound j.castSucc) F
        (Nat.le_of_lt (R.index_lt j))

/-- Every selected lower coarse complexity is in the common a priori
window. -/
theorem selectedGrowthCoarseComplexityBound_le_aPrioriWindow
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    selectedGrowthCoarseComplexityBound
        k r initialBound F R.index j ≤
      growthFunctionAPrioriWindow
        k r initialBound F γ := by
  calc
    selectedGrowthCoarseComplexityBound
          k r initialBound F R.index j =
        selectedGrowthCoarseLayerComplexityBound
          k r initialBound F R.index j.castSucc := by
      simp [selectedGrowthCoarseLayerComplexityBound]
    _ ≤
        growthFunctionAPrioriFineLayerBound
          k r initialBound F γ j.castSucc :=
      R.selectedCoarseLayerComplexityBound_le_aPriori
        j.castSucc
    _ ≤
        growthFunctionAPrioriWindow
          k r initialBound F γ :=
      growthFunctionAPrioriFineLayerBound_le_window
        k r initialBound F γ j.castSucc

/-- Every selected adjacent fine-upper numerical complexity is in the
common a priori window. -/
theorem selectedFineUpperComplexityBound_le_aPrioriWindow
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    R.selectedFineUpperComplexityBound j ≤
      growthFunctionAPrioriWindow
        k r initialBound F γ := by
  calc
    R.selectedFineUpperComplexityBound j =
        selectedGrowthFineLayerComplexityBound
          k r initialBound F R.index j.succ := by
      rfl
    _ ≤
        growthFunctionAPrioriFineLayerBound
          k r initialBound F γ j.succ :=
      R.selectedFineLayerComplexityBound_le_aPriori
        j.succ
    _ ≤
        growthFunctionAPrioriWindow
          k r initialBound F γ :=
      growthFunctionAPrioriFineLayerBound_le_window
        k r initialBound F γ j.succ

/-- Every selected adjacent coarse-upper numerical complexity is in the
common a priori window. -/
theorem selectedCoarseUpperComplexityBound_le_aPrioriWindow
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    R.selectedCoarseUpperComplexityBound j ≤
      growthFunctionAPrioriWindow
        k r initialBound F γ := by
  calc
    R.selectedCoarseUpperComplexityBound j =
        selectedGrowthCoarseLayerComplexityBound
          k r initialBound F R.index j.succ := by
      rfl
    _ ≤
        growthFunctionAPrioriFineLayerBound
          k r initialBound F γ j.succ :=
      R.selectedCoarseLayerComplexityBound_le_aPriori
        j.succ
    _ ≤
        growthFunctionAPrioriWindow
          k r initialBound F γ :=
      growthFunctionAPrioriFineLayerBound_le_window
        k r initialBound F γ j.succ

end GrowthFunctionOrderedComplexRegularityCertificate

/-! ## Pre-index selection with a certified common window -/

/-- Certificate existence together with all three finite-window hypotheses.
The window depends only on the input numerical schedules, never on the
selected energy-pigeonhole indices or on the ambient finite type. -/
theorem exists_growthFunctionCertificate_in_aPrioriWindow
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ)
    (hγ : ∀ j, 0 < γ j)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    ∃ R : GrowthFunctionOrderedComplexRegularityCertificate
        G k r initial initialBound F γ,
      (∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound F R.index j ≤
          growthFunctionAPrioriWindow
            k r initialBound F γ) ∧
      (∀ j : Fin r,
        R.selectedFineUpperComplexityBound j ≤
          growthFunctionAPrioriWindow
            k r initialBound F γ) ∧
      (∀ j : Fin r,
        R.selectedCoarseUpperComplexityBound j ≤
          growthFunctionAPrioriWindow
            k r initialBound F γ) := by
  obtain ⟨R⟩ :=
    GrowthFunctionOrderedComplexRegularityCertificate.nonempty
      initial initialBound F γ hγ hinitial
  exact ⟨R,
    R.selectedGrowthCoarseComplexityBound_le_aPrioriWindow,
    R.selectedFineUpperComplexityBound_le_aPrioriWindow,
    R.selectedCoarseUpperComplexityBound_le_aPrioriWindow⟩

/-! ## A canonical numerical scale and the synchronization inequality -/

/-- Choose one of the common scales supplied by the finite asymptotic
diagonal.  The choice depends only on `k`, `r`, the proposed window, and the
deletion allowance. -/
noncomputable def rankwiseChosenCommonScale
    (k r complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) : ℕ :=
  Classical.choose
    (exists_hierarchicalCommonScale_with_gap
      (Fintype.card (PositiveOrderedFace k r))
      (Fintype.card (OrderedPositiveSubface r))
      complexityBound hξ)

/-- All numerical properties of the chosen common scale. -/
theorem rankwiseChosenCommonScale_spec
    (k r complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    let Q :=
      rankwiseChosenCommonScale
        k r complexityBound hξ
    complexityBound + 2 ≤ Q ∧
      0 <
        hierarchicalCommonGap
          (Fintype.card (OrderedPositiveSubface r))
          complexityBound Q ξ ∧
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (complexityBound : ℝ) *
          hierarchicalCommonDensityFloor Q <
        ξ / 2 ∧
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (complexityBound : ℝ) *
          (hierarchicalCommonGap
              (Fintype.card (OrderedPositiveSubface r))
              complexityBound Q ξ /
            hierarchicalCommonTolerance Q) ≤
        ξ / 2 ∧
      (Fintype.card (PositiveOrderedFace k r) : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) <
        hierarchicalCommonDensityFloor Q ^
          Fintype.card (PositiveOrderedFace k r) := by
  exact Classical.choose_spec
    (exists_hierarchicalCommonScale_with_gap
      (Fintype.card (PositiveOrderedFace k r))
      (Fintype.card (OrderedPositiveSubface r))
      complexityBound hξ)

/-- Uniform positive count margin corresponding to a common finite
window. -/
noncomputable def hierarchicalCommonCountingMargin
    (k r complexityBound Q : ℕ) : ℝ :=
  hierarchicalCommonDensityFloor Q ^
      Fintype.card (PositiveOrderedFace k r) -
    (Fintype.card (PositiveOrderedFace k r) : ℝ) *
      (hierarchicalCommonDefectError Q +
        (complexityBound : ℝ) *
          hierarchicalCommonTolerance Q)

theorem rankwiseChosenCommonCountingMargin_pos
    (k r complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    0 <
      hierarchicalCommonCountingMargin
        k r complexityBound
          (rankwiseChosenCommonScale
            k r complexityBound hξ) := by
  have hspec :=
    rankwiseChosenCommonScale_spec
      k r complexityBound hξ
  unfold hierarchicalCommonCountingMargin
  dsimp only at hspec
  linarith

/-- The one unresolved self-bounding quantity, specialized to the
canonical numerical scale and the uniform initial complexity bound `2`
used for ordered patterns. -/
noncomputable def rankwiseChosenAPrioriWindow
    (k r complexityBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) : ℕ :=
  let Q :=
    rankwiseChosenCommonScale
      k r complexityBound hξ
  growthFunctionAPrioriWindow
    k r (fun _ => 2) (flooredGrowth Q)
    (fun _ =>
      hierarchicalCommonGap
        (Fintype.card (OrderedPositiveSubface r))
        complexityBound Q ξ)

/-- The canonical scale cannot synchronize with its own triangular
regularity window at positive rank.  This is not merely a missing estimate:
the requested self-bounding inequality is false for the current coupled
tolerance/complexity API. -/
theorem not_rankwiseChosenAPrioriWindow_le
    (k n complexityBound : ℕ)
    (hrk : n + 1 ≤ k)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ¬
      rankwiseChosenAPrioriWindow
          k (n + 1) complexityBound hξ ≤
        complexityBound := by
  let Q :=
    rankwiseChosenCommonScale
      k (n + 1) complexityBound hξ
  let γ : Fin (n + 1) → ℝ :=
    fun _ =>
      hierarchicalCommonGap
        (Fintype.card
          (OrderedPositiveSubface (n + 1)))
        complexityBound Q ξ
  have hQlarge :
      complexityBound + 2 ≤ Q := by
    have hspec :=
      rankwiseChosenCommonScale_spec
        k (n + 1) complexityBound hξ
    simpa [Q] using hspec.1
  have hnot :
      ¬
        growthFunctionAPrioriWindow
            k (n + 1) (fun _ => 2)
            (flooredGrowth Q) γ ≤
          complexityBound :=
    not_growthFunctionAPrioriWindow_le_of_bound_lt_floor
      k n complexityBound Q hrk (by omega) γ
  simpa [rankwiseChosenAPrioriWindow, Q, γ] using
    hnot

/-- Hence the synchronization premise used by the common-window removal
payload is globally unavailable at every positive admissible rank. -/
theorem no_rankwiseChosenWindowSynchronization
    (k n : ℕ) (hrk : n + 1 ≤ k) :
    ¬
      (∀ (ξ : ℝ) (hξ : 0 < ξ),
        ∃ complexityBound : ℕ,
          rankwiseChosenAPrioriWindow
              k (n + 1) complexityBound hξ ≤
            complexityBound) := by
  intro hsynchronize
  obtain ⟨complexityBound, hwindow⟩ :=
    hsynchronize 1 zero_lt_one
  exact
    (not_rankwiseChosenAPrioriWindow_le
      k n complexityBound hrk zero_lt_one)
      hwindow

/-! ## The uniform margin lies below every selected margin -/

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- Once the three preselected window hypotheses hold, the scalar common
margin is no larger than the literal selected margin.  Unlike the strict
counting theorem, this orientation exposes a threshold independent of the
ambient group and the input pattern. -/
theorem hierarchicalCommonCountingMargin_le_selected
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {γ : Fin r → ℝ}
    {complexityBound Q : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound (flooredGrowth Q) γ)
    (hcoarseWindow :
      ∀ j : Fin r,
        selectedGrowthCoarseComplexityBound
            k r initialBound (flooredGrowth Q) R.index j ≤
          complexityBound)
    (hfineUpperWindow :
      ∀ j : Fin r,
        R.selectedFineUpperComplexityBound j ≤
          complexityBound)
    (hQ : complexityBound + 1 ≤ Q) :
    hierarchicalCommonCountingMargin
          k r complexityBound Q ≤
      (∏ e : PositiveOrderedFace k r,
          R.selectedDensityFloor e.rank) -
        (∑ e : PositiveOrderedFace k r,
          (R.selectedDefectError e.rank +
            (R.selectedFineUpperComplexityBound
                e.lowerRank : ℝ) *
              R.selectedRankTolerance e.lowerRank)) := by
  have hQpos : 0 < Q := by omega
  have hsum :
      (∑ e : PositiveOrderedFace k r,
          (R.selectedDefectError e.rank +
            (R.selectedFineUpperComplexityBound
                e.lowerRank : ℝ) *
              R.selectedRankTolerance e.lowerRank)) ≤
        (Fintype.card (PositiveOrderedFace k r) : ℝ) *
          (hierarchicalCommonDefectError Q +
            (complexityBound : ℝ) *
              hierarchicalCommonTolerance Q) := by
    calc
      (∑ e : PositiveOrderedFace k r,
          (R.selectedDefectError e.rank +
            (R.selectedFineUpperComplexityBound
                e.lowerRank : ℝ) *
              R.selectedRankTolerance e.lowerRank)) ≤
          ∑ _e : PositiveOrderedFace k r,
            (hierarchicalCommonDefectError Q +
              (complexityBound : ℝ) *
                hierarchicalCommonTolerance Q) := by
        apply Finset.sum_le_sum
        intro e _he
        rw [R.selectedDefectError_positiveFace_rank,
          R.selectedRankDefectError_eq_common_of_window
            hcoarseWindow hQ e.lowerRank,
          R.selectedRankTolerance_eq_common_of_window
            hcoarseWindow hQ e.lowerRank]
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr
              (hfineUpperWindow e.lowerRank))
            (hierarchicalCommonTolerance_pos hQpos).le)
          _
      _ =
          (Fintype.card (PositiveOrderedFace k r) : ℝ) *
            (hierarchicalCommonDefectError Q +
              (complexityBound : ℝ) *
                hierarchicalCommonTolerance Q) := by
        simp [mul_add]
  have hprod :
      (∏ e : PositiveOrderedFace k r,
          R.selectedDensityFloor e.rank) =
        hierarchicalCommonDensityFloor Q ^
          Fintype.card (PositiveOrderedFace k r) := by
    calc
      (∏ e : PositiveOrderedFace k r,
          R.selectedDensityFloor e.rank) =
          ∏ _e : PositiveOrderedFace k r,
            hierarchicalCommonDensityFloor Q := by
        apply Finset.prod_congr rfl
        intro e _he
        rw [R.selectedDensityFloor_positiveFace_rank]
        exact
          R.selectedRankDensityFloor_eq_common_of_window
            hcoarseWindow hQ e.lowerRank
      _ =
          hierarchicalCommonDensityFloor Q ^
            Fintype.card (PositiveOrderedFace k r) := by
        simp
  rw [hprod]
  unfold hierarchicalCommonCountingMargin
  linarith

end GrowthFunctionOrderedComplexRegularityCertificate

/-! ## Uniform-removal-ready closure -/

/-- The whole ordered removal theorem follows once the single synchronized
window inequality has a solution for every positive deletion allowance.

All quantifiers required for uniformity are in their final order: the
window, common growth value, gap schedule, and positive count threshold are
chosen before the ambient type and the ordered pattern.  Certificate
nonemptiness then supplies the coarse/fine complex inside that same window.
-/
theorem hasUniformOrderedPatternRemoval_of_rankwiseWindowSynchronization
    (k n : ℕ) (hrk : n + 1 ≤ k)
    (hsynchronize :
      ∀ (ξ : ℝ) (hξ : 0 < ξ),
        ∃ complexityBound : ℕ,
          rankwiseChosenAPrioriWindow
              k (n + 1) complexityBound hξ ≤
            complexityBound) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  obtain ⟨complexityBound, hwindowChosen⟩ :=
    hsynchronize ξ hξ
  let Q : ℕ :=
    rankwiseChosenCommonScale
      k (n + 1) complexityBound hξ
  let γ : Fin (n + 1) → ℝ :=
    fun _ =>
      hierarchicalCommonGap
        (Fintype.card
          (OrderedPositiveSubface (n + 1)))
        complexityBound Q ξ
  let c : ℝ :=
    hierarchicalCommonCountingMargin
      k (n + 1) complexityBound Q
  have hspec :
      complexityBound + 2 ≤ Q ∧
        0 <
          hierarchicalCommonGap
            (Fintype.card
              (OrderedPositiveSubface (n + 1)))
            complexityBound Q ξ ∧
        (Fintype.card
            (OrderedPositiveSubface (n + 1)) : ℝ) *
            (complexityBound : ℝ) *
            hierarchicalCommonDensityFloor Q <
          ξ / 2 ∧
        (Fintype.card
            (OrderedPositiveSubface (n + 1)) : ℝ) *
            (complexityBound : ℝ) *
            (hierarchicalCommonGap
                (Fintype.card
                  (OrderedPositiveSubface (n + 1)))
                complexityBound Q ξ /
              hierarchicalCommonTolerance Q) ≤
          ξ / 2 ∧
        (Fintype.card
            (PositiveOrderedFace k (n + 1)) : ℝ) *
            (hierarchicalCommonDefectError Q +
              (complexityBound : ℝ) *
                hierarchicalCommonTolerance Q) <
          hierarchicalCommonDensityFloor Q ^
            Fintype.card
              (PositiveOrderedFace k (n + 1)) := by
    simpa [Q] using
      (rankwiseChosenCommonScale_spec
        k (n + 1) complexityBound hξ)
  rcases hspec with
    ⟨hQ, hgapPos, hclean, _hgapCost, hcount⟩
  have hc : 0 < c := by
    simpa [c, Q] using
      (rankwiseChosenCommonCountingMargin_pos
        k (n + 1) complexityBound hξ)
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty
    H hHcount
  have hwindow :
      growthFunctionAPrioriWindow
          k (n + 1) (fun _ => 2)
          (flooredGrowth Q) γ ≤
        complexityBound := by
    simpa [rankwiseChosenAPrioriWindow, Q, γ] using
      hwindowChosen
  have hγ : ∀ j, 0 < γ j := by
    intro j
    simpa [γ] using hgapPos
  obtain ⟨R, hcoarseA, hfineA, hcoarseUpperA⟩ :=
    exists_growthFunctionCertificate_in_aPrioriWindow
      (orderedPatternInitialComplex H)
      (fun _ => 2)
      (flooredGrowth Q) γ hγ
      (complexity_orderedPatternInitialComplex_le_two H)
  have hcoarseWindow :
      ∀ j : Fin (n + 1),
        selectedGrowthCoarseComplexityBound
            k (n + 1) (fun _ => 2)
              (flooredGrowth Q) R.index j ≤
          complexityBound :=
    fun j => (hcoarseA j).trans hwindow
  have hfineWindow :
      ∀ j : Fin (n + 1),
        R.selectedFineUpperComplexityBound j ≤
          complexityBound :=
    fun j => (hfineA j).trans hwindow
  have hcoarseUpperWindow :
      ∀ j : Fin (n + 1),
        R.selectedCoarseUpperComplexityBound j ≤
          complexityBound :=
    fun j => (hcoarseUpperA j).trans hwindow
  have hmargin :
      c ≤
        (∏ e : PositiveOrderedFace k (n + 1),
            R.selectedDensityFloor e.rank) -
          (∑ e : PositiveOrderedFace k (n + 1),
            (R.selectedDefectError e.rank +
              (R.selectedFineUpperComplexityBound
                  e.lowerRank : ℝ) *
                R.selectedRankTolerance
                  e.lowerRank)) := by
    simpa [c] using
      R.hierarchicalCommonCountingMargin_le_selected
        hcoarseWindow hfineWindow (by omega)
  refine ⟨R.selectedCoarseBadBaseDeletionFamily, ?_, ?_⟩
  · apply R.selectedCoarseBadBaseDeletionFamily_isCover
      hrk H
    exact hHcount.trans_le hmargin
  · intro e
    have hdelete :
        OrderedPattern.faceDeletionDensity
            R.selectedCoarseBadBaseDeletionFamily e <
          ξ := by
      simpa [γ] using
        R.faceDeletionDensity_selectedCoarseBadBase_lt_of_window
          hξ hcoarseWindow hfineWindow
          hcoarseUpperWindow hQ hclean e
    exact hdelete.le

/-! ## Decoupled rankwise coarse-target schedules

The preceding impossibility uses the same reciprocal `1 / F(M)` for
preliminary regularity, localized good-atom defect, and density selection.
The general counting and cleaning theorems do not require that
identification.  This section records the narrow decoupled interface they
actually consume.

Compared with `StageIndexedCoarseTargetRemovalSchedule`, the cleaning
complexity is the exact adjacent coarse-upper bound at rank `j + 1`.
Consequently the current rank's new regularity step is never charged to its
own cleaning loss.  Density floors, localized defect thresholds, and defect
errors may vary by selected rank and by the complete finite stage vector.
-/

/-- A stage-indexed schedule with independent preliminary-regularity,
density, localized-defect, and defect-error parameters, using the exact
adjacent coarse-upper complexity at every rank. -/
structure RankwiseStageIndexedCoarseTargetRemovalSchedule
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
    ∀ index j, 0 ≤ densityFloor index j
  defectThreshold_pos :
    ∀ index j, 0 < defectThreshold index j
  defectError_nonneg :
    ∀ index j, 0 ≤ defectError index j
  defectThreshold_le_sq :
    ∀ index j,
      defectThreshold index j ≤
        (defectError index j) ^ 2
  countThreshold_pos : 0 < countThreshold
  uniform_counting_margin :
    ∀ index : CoarseTargetStageIndex length,
      countThreshold ≤
        (∏ e : PositiveOrderedFace k r,
          densityFloor index e.lowerRank) -
          (∑ e : PositiveOrderedFace k r,
            (defectError index e.lowerRank +
              tolerance e.lowerRank
                (index e.lowerRank).1))
  uniform_deletion_margin :
    ∀ index : CoarseTargetStageIndex length,
      (∑ q : OrderedPositiveSubface r,
        (((CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
                r initialBound budget length index q.1 : ℕ) : ℝ) *
            densityFloor index q.1 +
          ((Fintype.card
              (OrderedFace k (q.1.1 + 1)) : ℝ) /
                (length q.1 : ℝ)) /
            defectThreshold index q.1)) ≤
        ξ

/-- Existence of the decoupled schedules needed at every positive removal
allowance. -/
def HasRankwiseStageIndexedCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (RankwiseStageIndexedCoarseTargetRemovalSchedule
        k r initialBound ξ)

namespace RankwiseStageIndexedCoarseTargetRemovalSchedule

/-- The decoupled numerical schedule feeds directly into the existing
coarse-target regularity selector. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : RankwiseStageIndexedCoarseTargetRemovalSchedule
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

/-- One selected certificate produces the exact rankwise cover and
deletion payload.  This is the generalized good-atom wrapper: preliminary
regularity uses `tolerance`, while cleaning uses the independent
`densityFloor` and `defectThreshold`. -/
theorem certificateRemoval
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n initialBound : ℕ} {ξ : ℝ}
    (hrk : n + 1 ≤ k)
    (S : RankwiseStageIndexedCoarseTargetRemovalSchedule
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
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  let index : CoarseTargetStageIndex S.length :=
    R.stageIndex
  let ρ : Fin (n + 1) → ℝ :=
    S.densityFloor index
  let β : Fin (n + 1) → ℝ :=
    S.defectThreshold index
  let δ : Fin (n + 1) → ℝ :=
    S.defectError index
  let αs : ℕ → ℝ :=
    positiveRankSchedule ρ
  let βs : ℕ → ℝ :=
    positiveRankSchedule β
  let δs : ℕ → ℝ :=
    positiveRankSchedule δ
  let τ : OrderedRegularityTolerance (n + 1) :=
    selectedOrderedComplexTolerance
      S.tolerance R.index
  let upperBound : Fin (n + 1) → ℕ :=
    fun j =>
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
          (n + 1) initialBound S.budget
          S.length index j
  let D : OrderedPattern.DeletionFamily
      (G := G) k (n + 1) :=
    R.toCoarseFine.orderedCoarseBadBaseDeletionFamily
      αs βs
  have hαs : ∀ m, 0 ≤ αs m := by
    exact positiveRankSchedule_nonneg
      (S.densityFloor_nonneg index)
  have hβs : ∀ m, 0 < βs m := by
    exact positiveRankSchedule_pos
      (S.defectThreshold_pos index)
  have hδs : ∀ m, 0 ≤ δs m := by
    exact positiveRankSchedule_nonneg
      (S.defectError_nonneg index)
  have hβδ : ∀ m, βs m ≤ (δs m) ^ 2 := by
    intro m
    by_cases hm : 0 < m ∧ m ≤ n + 1
    · simpa [βs, δs, positiveRankSchedule,
        hm, β, δ] using
        S.defectThreshold_le_sq index
          ⟨m - 1, by omega⟩
    · simp [βs, δs, positiveRankSchedule, hm]
  have hτ : ∀ j, 0 ≤ τ j := by
    intro j
    exact (S.tolerance_pos j (R.index j)).le
  have hcount' :
      H.toWeighted.patternCount <
        (∏ e : PositiveOrderedFace k (n + 1),
            αs e.rank) -
          (∑ e : PositiveOrderedFace k (n + 1),
            (δs e.rank + τ e.lowerRank)) := by
    apply lt_of_lt_of_le hcount
    simpa [αs, δs, τ, ρ, δ, index,
      PositiveOrderedFace.rank,
      selectedOrderedComplexTolerance,
      CoarseTargetOrderedComplexRegularityCertificate.stageIndex] using
      S.uniform_counting_margin index
  have hcover : H.IsCover D := by
    apply
      orderedCoarseBadBaseDeletionFamily_isCover_rankwise
        hrk H R.toCoarseFine
        R.coarse_refines_initial
        αs βs τ
        R.isFullyMixedPreliminaryOrderedRegular
        δs hαs hτ hδs
        (fun m => (hβs m).le)
        hβδ hcount'
  refine ⟨D, hcover, ?_⟩
  intro e
  have hcoarse :
      ∀ (j : Fin (n + 1))
          (f : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
            (R.coarse.partition j.succ f) ≤
          upperBound j := by
    intro j f
    simpa [upperBound, index] using
      R.coarse_upper_complexity_le_selectedUpperBound
        hinitial j f
  have hdelete :=
    R.faceDeletionDensity_orderedCoarseBadBase_rankwise_le
      upperBound hcoarse αs βs
      (fun j => hαs (j + 1))
      (fun j => hβs (j + 1)) e
  refine hdelete.trans ?_
  simpa [upperBound, αs, βs, ρ, β, index] using
    S.uniform_deletion_margin index

end RankwiseStageIndexedCoarseTargetRemovalSchedule

/-! ### Conditional uniform assembly for the decoupled selector -/

/-- Rankwise stage-indexed schedule existence is sufficient for uniform
ordered-pattern removal.  Unlike the common-window premise above, this
selector is not contradicted by the triangular one-step lower bound. -/
theorem hasUniformOrderedPatternRemoval_succ_of_rankwiseStageSchedules
    (k n : ℕ) (hrk : n + 1 ≤ k)
    (hschedules :
      HasRankwiseStageIndexedCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  let S :
      RankwiseStageIndexedCoarseTargetRemovalSchedule
        k (n + 1) 2 ξ :=
    Classical.choice (hschedules ξ hξ)
  refine ⟨S.countThreshold, S.countThreshold_pos, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty
    H hcount
  obtain ⟨R⟩ :=
    S.certificate_nonempty
      (orderedPatternInitialComplex H)
  exact S.certificateRemoval
    hrk H R
    (complexity_orderedPatternInitialComplex_le_two H)
    hcount

/-! ### The next exact obstruction: uniformity over every stage vector

The exact adjacent-rank shift removes the spurious rank-one feedback.
Starting at rank two, however, asking the numerical margin to hold at
*every* possible energy-pigeonhole index is still too strong.  At the last
rank-one stage, the rank-one tower factor bounds the rank-one length from
below.  Cleaning at rank one needs that length times the square defect to
be large, while counting and lower-rank cleaning force the same product to
be strictly below one.

Thus the final selector must correlate its admissible stage vector with the
actual small-energy-gap witness.  Merely allowing parameters to depend on
an arbitrary finite stage vector does not encode that stopping-time
correlation.
-/

/-- A fixed-upper tower complexity factor is always positive. -/
theorem fixedUpperLayerComplexityFactor_pos
    (j : ℕ) (budget : ℕ → ℕ) :
    ∀ n, 0 < fixedUpperLayerComplexityFactor j budget n := by
  intro n
  induction n with
  | zero =>
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      rw [fixedUpperLayerComplexityFactor]
      exact Nat.mul_pos (by positivity) ih

/-- Every positive-budget fixed-upper tower grows by at least one at every
stage, in every rank. -/
theorem succ_le_fixedUpperLayerComplexityFactor
    (j : ℕ) (budget : ℕ → ℕ)
    (hbudget : ∀ n, 0 < budget n) :
    ∀ n,
      n + 1 ≤ fixedUpperLayerComplexityFactor j budget n := by
  intro n
  induction n with
  | zero =>
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      rw [fixedUpperLayerComplexityFactor]
      have hbase : 2 ≤ 2 ^ (j + 1) := by
        simpa using
          Nat.pow_le_pow_right
            (by omega : 0 < (2 : ℕ))
            (by omega : 0 < j + 1)
      have hpow :
          2 ≤ (2 ^ (j + 1)) ^ budget n := by
        exact hbase.trans
          (by
            simpa using
              Nat.pow_le_pow_right
                (by positivity :
                  0 < 2 ^ (j + 1))
                (hbudget n))
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤
            (2 ^ (j + 1)) ^ budget n *
              fixedUpperLayerComplexityFactor j budget n :=
          Nat.mul_le_mul hpow ih

/-- At the all-last rank-two stage vector, the rank-one energy length is
bounded by the exact adjacent coarse-upper bound charged to rank-one
subfaces. -/
theorem length_one_le_coarseTargetSelectedUpperComplexityBound_two_last
    {initialBound : ℕ}
    (budget : (j : Fin 2) → ℕ → ℕ)
    (length : Fin 2 → ℕ)
    (hinitialBound : 0 < initialBound)
    (hlength : ∀ j, 0 < length j)
    (hbudget : ∀ n, 0 < budget 1 n) :
    length 1 ≤
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
        2 initialBound budget length
          (lastCoarseTargetStageIndex hlength) 0 := by
  have hfactor :=
    succ_le_fixedUpperLayerComplexityFactor
      1 (budget 1) hbudget (length 1 - 1)
  have hsub : length 1 - 1 + 1 = length 1 := by
    have := hlength 1
    omega
  have hfactor' :
      length 1 ≤
        fixedUpperLayerComplexityFactor
          1 (budget 1) (length 1 - 1) := by
    simpa [hsub] using hfactor
  rw [
    CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
    dif_pos (by omega)]
  change
    length 1 ≤
      initialBound *
        fixedUpperLayerComplexityFactor
          1 (budget 1) (length 1 - 1)
  calc
    length 1 ≤
        fixedUpperLayerComplexityFactor
          1 (budget 1) (length 1 - 1) :=
      hfactor'
    _ ≤
        initialBound *
          fixedUpperLayerComplexityFactor
            1 (budget 1) (length 1 - 1) := by
      exact Nat.le_mul_of_pos_left _
        hinitialBound

/-- Even the rankwise exact-upper schedule is impossible at rank two if it
must work for every stage vector.  This pinpoints the remaining API
mismatch: the selector must expose a favorable stopping-time witness, not a
uniform numerical payload on the entire stage box. -/
theorem not_hasRankwiseStageIndexedCoarseTargetRemovalSchedules_two
    (k initialBound : ℕ)
    (hk : 2 ≤ k) (hinitialBound : 0 < initialBound) :
    ¬ HasRankwiseStageIndexedCoarseTargetRemovalSchedules
      k 2 initialBound := by
  intro hschedules
  obtain ⟨S⟩ := hschedules 1 (by norm_num)
  let index : CoarseTargetStageIndex S.length :=
    lastCoarseTargetStageIndex S.length_pos
  let upper : Fin 2 → ℕ :=
    fun j =>
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
        2 initialBound S.budget S.length index j
  let ρ : Fin 2 → ℝ :=
    S.densityFloor index
  let β : Fin 2 → ℝ :=
    S.defectThreshold index
  let δ : Fin 2 → ℝ :=
    S.defectError index
  let cleaningTerm : OrderedPositiveSubface 2 → ℝ :=
    fun q =>
      (upper q.1 : ℝ) * ρ q.1 +
        ((Fintype.card
            (OrderedFace k (q.1.1 + 1)) : ℝ) /
              (S.length q.1 : ℝ)) /
          β q.1
  let product : ℝ :=
    ∏ e : PositiveOrderedFace k 2, ρ e.lowerRank
  let errorSum : ℝ :=
    ∑ e : PositiveOrderedFace k 2,
      (δ e.lowerRank +
        S.tolerance e.lowerRank
          (index e.lowerRank).1)
  let q0 : OrderedPositiveSubface 2 :=
    ⟨0, Fin.castLEOrderEmb (by omega)⟩
  let q1 : OrderedPositiveSubface 2 :=
    ⟨1, Fin.castLEOrderEmb (by omega)⟩
  let e0 : PositiveOrderedFace k 2 :=
    ⟨0, Fin.castLEOrderEmb (by omega)⟩
  let e1 : PositiveOrderedFace k 2 :=
    ⟨1, Fin.castLEOrderEmb hk⟩
  have hbudget1 : ∀ n, 0 < S.budget 1 n := by
    intro n
    by_contra hnot
    have hzero : S.budget 1 n = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hspec := S.budget_spec (1 : Fin 2) n
    rw [hzero] at hspec
    norm_num at hspec
    exact
      (not_lt_of_ge
        (Nat.cast_nonneg
          (Fintype.card (OrderedFace k 2)))) hspec
  have hlengthUpper : S.length 1 ≤ upper 0 := by
    exact
      length_one_le_coarseTargetSelectedUpperComplexityBound_two_last
        S.budget S.length hinitialBound S.length_pos
        hbudget1
  have hupperPos : ∀ j, 0 < upper j := by
    intro j
    unfold upper
    by_cases hj : j.1 + 1 < 2
    · rw [
        CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
        dif_pos hj]
      exact Nat.mul_pos hinitialBound
        (by
          apply fixedUpperLayerComplexityFactor_pos)
    · rw [
        CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
        dif_neg hj]
      exact hinitialBound
  have hρnonneg : ∀ j, 0 ≤ ρ j := by
    intro j
    exact S.densityFloor_nonneg index j
  have hβpos : ∀ j, 0 < β j := by
    intro j
    exact S.defectThreshold_pos index j
  have hδnonneg : ∀ j, 0 ≤ δ j := by
    intro j
    exact S.defectError_nonneg index j
  have hcleaningTerm_nonneg :
      ∀ q, 0 ≤ cleaningTerm q := by
    intro q
    apply add_nonneg
    · exact mul_nonneg (by positivity) (hρnonneg q.1)
    · exact div_nonneg
        (div_nonneg (by positivity)
          (by
            exact_mod_cast (S.length_pos q.1).le))
        (hβpos q.1).le
  have hdeletion :
      (∑ q : OrderedPositiveSubface 2,
          cleaningTerm q) ≤ 1 := by
    simpa [cleaningTerm, upper, ρ, β, index] using
      S.uniform_deletion_margin index
  have hterm_le (q : OrderedPositiveSubface 2) :
      cleaningTerm q ≤ 1 := by
    exact
      (Finset.single_le_sum
        (fun p _ => hcleaningTerm_nonneg p)
        (Finset.mem_univ q)).trans hdeletion
  have hupperRho_le (j : Fin 2)
      (q : OrderedPositiveSubface 2) (hq : q.1 = j) :
      (upper j : ℝ) * ρ j ≤ 1 := by
    calc
      (upper j : ℝ) * ρ j =
          (upper q.1 : ℝ) * ρ q.1 := by rw [hq]
      _ ≤ cleaningTerm q := by
        exact le_add_of_nonneg_right
          (div_nonneg
            (div_nonneg (by positivity)
              (by
                exact_mod_cast (S.length_pos q.1).le))
            (hβpos q.1).le)
      _ ≤ 1 := hterm_le q
  have hupperRho0_le :
      (upper 0 : ℝ) * ρ 0 ≤ 1 :=
    hupperRho_le 0 q0 (by rfl)
  have hupperRho1_le :
      (upper 1 : ℝ) * ρ 1 ≤ 1 :=
    hupperRho_le 1 q1 (by rfl)
  have hρle : ∀ j, ρ j ≤ 1 := by
    intro j
    have hu : (1 : ℝ) ≤ (upper j : ℝ) := by
      exact_mod_cast hupperPos j
    calc
      ρ j = 1 * ρ j := by ring
      _ ≤ (upper j : ℝ) * ρ j :=
        mul_le_mul_of_nonneg_right hu (hρnonneg j)
      _ ≤ 1 := by
        fin_cases j
        · exact hupperRho0_le
        · exact hupperRho1_le
  have hcount := S.uniform_counting_margin index
  have herror_lt_product : errorSum < product := by
    dsimp only [errorSum, product, ρ, δ] at hcount ⊢
    linarith [S.countThreshold_pos]
  have herrorTerm_nonneg :
      ∀ e : PositiveOrderedFace k 2,
        0 ≤
          δ e.lowerRank +
            S.tolerance e.lowerRank
              (index e.lowerRank).1 := by
    intro e
    exact add_nonneg (hδnonneg e.lowerRank)
      (S.tolerance_pos _ _).le
  have hδ1_lt_product : δ 1 < product := by
    have hsingle :
        δ e1.lowerRank +
              S.tolerance e1.lowerRank
                (index e1.lowerRank).1 ≤
            errorSum := by
      exact Finset.single_le_sum
        (fun e _ => herrorTerm_nonneg e)
        (Finset.mem_univ e1)
    have hδle :
        δ 1 ≤
          δ e1.lowerRank +
            S.tolerance e1.lowerRank
              (index e1.lowerRank).1 := by
      calc
        δ 1 = δ e1.lowerRank := by simp [e1]
        _ ≤
            δ e1.lowerRank +
              S.tolerance e1.lowerRank
                (index e1.lowerRank).1 :=
          le_add_of_nonneg_right
            (S.tolerance_pos e1.lowerRank
              (index e1.lowerRank).1).le
    exact (hδle.trans hsingle).trans_lt
      herror_lt_product
  have hδ1pos : 0 < δ 1 := by
    have hβδ :=
      S.defectThreshold_le_sq index (1 : Fin 2)
    have hsqpos : 0 < (δ 1) ^ 2 :=
      (hβpos 1).trans_le hβδ
    by_contra hnot
    have hzero : δ 1 = 0 :=
      le_antisymm (not_lt.mp hnot) (hδnonneg 1)
    simp [hzero] at hsqpos
  have hproductPos : 0 < product :=
    hδ1pos.trans hδ1_lt_product
  have hρ0pos : 0 < ρ 0 := by
    by_contra hnot
    have hρzero : ρ 0 = 0 :=
      le_antisymm (not_lt.mp hnot) (hρnonneg 0)
    have he0zero : ρ e0.lowerRank = 0 := by
      simpa [e0] using hρzero
    have hproductZero : product = 0 := by
      exact Finset.prod_eq_zero
        (Finset.mem_univ e0) he0zero
    rw [hproductZero] at hproductPos
    exact (lt_irrefl 0) hproductPos
  have hproduct_le_rho0 : product ≤ ρ 0 := by
    have hrest :
        (∏ e ∈
            (Finset.univ :
              Finset (PositiveOrderedFace k 2)).erase e0,
            ρ e.lowerRank) ≤ 1 := by
      apply Finset.prod_le_one₀
      · intro e _he
        exact hρnonneg e.lowerRank
      · intro e _he
        exact hρle e.lowerRank
    have hsplit :
        product =
          ρ e0.lowerRank *
            ∏ e ∈
              (Finset.univ :
                Finset (PositiveOrderedFace k 2)).erase e0,
              ρ e.lowerRank := by
      exact
        (Finset.mul_prod_erase
          (Finset.univ :
            Finset (PositiveOrderedFace k 2))
          (fun e => ρ e.lowerRank)
          (Finset.mem_univ e0)).symm
    rw [hsplit]
    simpa [e0] using
      mul_le_mul_of_nonneg_left hrest (hρnonneg 0)
  have hδrho : δ 1 < ρ 0 :=
    hδ1_lt_product.trans_le hproduct_le_rho0
  have hβrho :
      β 1 < (ρ 0) ^ 2 := by
    exact
      (S.defectThreshold_le_sq index (1 : Fin 2)).trans_lt
        ((sq_lt_sq₀ (hδnonneg 1) (hρ0pos.le)).2
          hδrho)
  have hgap1_le :
      ((Fintype.card (OrderedFace k 2) : ℝ) /
          (S.length 1 : ℝ)) / β 1 ≤ 1 := by
    have hleftNonneg :
        0 ≤ (upper q1.1 : ℝ) * ρ q1.1 :=
      mul_nonneg (by positivity) (hρnonneg q1.1)
    calc
      ((Fintype.card (OrderedFace k 2) : ℝ) /
            (S.length 1 : ℝ)) /
          β 1 ≤
          (upper q1.1 : ℝ) * ρ q1.1 +
            ((Fintype.card (OrderedFace k 2) : ℝ) /
                (S.length 1 : ℝ)) /
              β 1 :=
        le_add_of_nonneg_left hleftNonneg
      _ = cleaningTerm q1 := by
        simp [cleaningTerm, q1]
      _ ≤ 1 := hterm_le q1
  have hfacePos :
      0 < Fintype.card (OrderedFace k 2) :=
    card_orderedFace_pos_of_le hk
  have hlengthPos : (0 : ℝ) < S.length 1 := by
    exact_mod_cast S.length_pos 1
  have hface_le_lengthBeta :
      (Fintype.card (OrderedFace k 2) : ℝ) ≤
        (S.length 1 : ℝ) * β 1 := by
    have hdiv_le_beta :
        (Fintype.card (OrderedFace k 2) : ℝ) /
            (S.length 1 : ℝ) ≤
          β 1 := by
      have := (div_le_iff₀ (hβpos 1)).1 hgap1_le
      simpa using this
    simpa [mul_comm] using
      (div_le_iff₀ hlengthPos).1 hdiv_le_beta
  have hone_lt_lengthRho :
      (1 : ℝ) <
        (S.length 1 : ℝ) * (ρ 0) ^ 2 := by
    have hfaceOne :
        (1 : ℝ) ≤
          (Fintype.card (OrderedFace k 2) : ℝ) := by
      exact_mod_cast hfacePos
    have hstrict :
        (S.length 1 : ℝ) * β 1 <
          (S.length 1 : ℝ) * (ρ 0) ^ 2 :=
      mul_lt_mul_of_pos_left hβrho hlengthPos
    exact
      (hfaceOne.trans hface_le_lengthBeta).trans_lt
        hstrict
  have hupperRhoSq_le :
      ((upper 0 : ℝ) * ρ 0) ^ 2 ≤ 1 := by
    simpa using
      (sq_le_sq₀
        (mul_nonneg (by positivity) (hρnonneg 0))
        (by norm_num : (0 : ℝ) ≤ 1)).2
          hupperRho0_le
  have hupper_le_sq :
      (upper 0 : ℝ) ≤ (upper 0 : ℝ) ^ 2 := by
    have hu : (1 : ℝ) ≤ (upper 0 : ℝ) := by
      exact_mod_cast hupperPos 0
    calc
      (upper 0 : ℝ) =
          (upper 0 : ℝ) * 1 := by ring
      _ ≤ (upper 0 : ℝ) * (upper 0 : ℝ) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = (upper 0 : ℝ) ^ 2 := by ring
  have hupperRhoSq' :
      (upper 0 : ℝ) * (ρ 0) ^ 2 ≤ 1 := by
    calc
      (upper 0 : ℝ) * (ρ 0) ^ 2 ≤
          (upper 0 : ℝ) ^ 2 * (ρ 0) ^ 2 :=
        mul_le_mul_of_nonneg_right hupper_le_sq
          (sq_nonneg (ρ 0))
      _ = ((upper 0 : ℝ) * ρ 0) ^ 2 := by ring
      _ ≤ 1 := hupperRhoSq_le
  have hlengthUpperCast :
      (S.length 1 : ℝ) ≤ (upper 0 : ℝ) := by
    exact_mod_cast hlengthUpper
  have hlengthRho_le :
      (S.length 1 : ℝ) * (ρ 0) ^ 2 ≤ 1 := by
    exact
      (mul_le_mul_of_nonneg_right
        hlengthUpperCast (sq_nonneg (ρ 0))).trans
          hupperRhoSq'
  exact (not_lt_of_ge hlengthRho_le)
    hone_lt_lengthRho

/-! ## Compatibility at the actual stopping-time witness

The two negative results above rule out bounds imposed on a preselected
window or on every point of a finite stage box.  The semantic removal
argument only needs the inequalities at the certificate's *actual*
energy-pigeonhole witness.  The following structure is the narrow
certificate-level interface for precisely that payload.
-/

/-- Rankwise cleaning and counting data attached to one selected
coarse-target regularity certificate.

Unlike a stage-box schedule, the upper bounds and atom thresholds are data
at `R.index`; no assertion is made about stage vectors the regularity
selector did not choose. -/
structure RankwiseSelectedCoarseTargetCompatibility
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (ξ c : ℝ) where
  upperBound : Fin r → ℕ
  densityFloor : Fin r → ℝ
  defectThreshold : Fin r → ℝ
  defectError : Fin r → ℝ
  densityFloor_nonneg :
    ∀ j, 0 ≤ densityFloor j
  defectThreshold_pos :
    ∀ j, 0 < defectThreshold j
  defectError_nonneg :
    ∀ j, 0 ≤ defectError j
  tolerance_nonneg :
    ∀ j,
      0 ≤ selectedOrderedComplexTolerance
        ε R.index j
  defectThreshold_le_sq :
    ∀ j,
      defectThreshold j ≤ (defectError j) ^ 2
  counting_margin :
    c ≤
      (∏ e : PositiveOrderedFace k r,
        densityFloor e.lowerRank) -
        (∑ e : PositiveOrderedFace k r,
          (defectError e.lowerRank +
            selectedOrderedComplexTolerance
              ε R.index e.lowerRank))
  coarse_upper_complexity :
    ∀ (j : Fin r)
        (e : OrderedFace k (j.1 + 1)),
      FacePartition.complexity
          (R.coarse.partition j.succ e) ≤
        upperBound j
  deletion_margin :
    (∑ q : OrderedPositiveSubface r,
      ((upperBound q.1 : ℝ) *
          densityFloor q.1 +
        ((Fintype.card
            (OrderedFace k (q.1.1 + 1)) : ℝ) /
              (length q.1 : ℝ)) /
          defectThreshold q.1)) ≤
      ξ

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- The narrow generalized good-atom wrapper: compatibility at the actual
selected certificate produces a semantic cover and the requested rankwise
deletion bound. -/
theorem removal_of_rankwiseSelectedCompatibility
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
    {ξ c : ℝ}
    (C : RankwiseSelectedCoarseTargetCompatibility
      R ξ c)
    (hcount : H.toWeighted.patternCount < c) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k (n + 1),
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  let αs : ℕ → ℝ :=
    positiveRankSchedule C.densityFloor
  let βs : ℕ → ℝ :=
    positiveRankSchedule C.defectThreshold
  let δs : ℕ → ℝ :=
    positiveRankSchedule C.defectError
  let τ : OrderedRegularityTolerance (n + 1) :=
    selectedOrderedComplexTolerance ε R.index
  let D : OrderedPattern.DeletionFamily
      (G := G) k (n + 1) :=
    R.toCoarseFine.orderedCoarseBadBaseDeletionFamily
      αs βs
  have hαs : ∀ m, 0 ≤ αs m :=
    positiveRankSchedule_nonneg
      C.densityFloor_nonneg
  have hβs : ∀ m, 0 < βs m :=
    positiveRankSchedule_pos
      C.defectThreshold_pos
  have hδs : ∀ m, 0 ≤ δs m :=
    positiveRankSchedule_nonneg
      C.defectError_nonneg
  have hβδ : ∀ m, βs m ≤ (δs m) ^ 2 := by
    intro m
    by_cases hm : 0 < m ∧ m ≤ n + 1
    · simpa [βs, δs, positiveRankSchedule, hm] using
        C.defectThreshold_le_sq
          ⟨m - 1, by omega⟩
    · simp [βs, δs, positiveRankSchedule, hm]
  have hcount' :
      H.toWeighted.patternCount <
        (∏ e : PositiveOrderedFace k (n + 1),
            αs e.rank) -
          (∑ e : PositiveOrderedFace k (n + 1),
            (δs e.rank + τ e.lowerRank)) := by
    apply lt_of_lt_of_le hcount
    simpa [αs, δs, τ,
      PositiveOrderedFace.rank,
      selectedOrderedComplexTolerance] using
      C.counting_margin
  have hcover : H.IsCover D := by
    apply
      orderedCoarseBadBaseDeletionFamily_isCover_rankwise
        hrank H R.toCoarseFine hinitial
        αs βs τ
        R.isFullyMixedPreliminaryOrderedRegular
        δs hαs C.tolerance_nonneg hδs
        (fun m => (hβs m).le)
        hβδ hcount'
  refine ⟨D, hcover, ?_⟩
  intro e
  have hdelete :=
    R.faceDeletionDensity_orderedCoarseBadBase_rankwise_le
      C.upperBound C.coarse_upper_complexity
      αs βs
      (fun j => hαs (j + 1))
      (fun j => hβs (j + 1)) e
  refine hdelete.trans ?_
  simpa [αs, βs] using C.deletion_margin

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## An ambient-independent correlated selector

The remaining numerical theorem should construct the following object.
Its schedules and positive count threshold are chosen before the ambient
finite type and input complex.  Its `select` field is allowed to choose the
regularity certificate and prove compatibility together, so the numerical
payload is required only at the actual stopping-time path.
-/

/-- Ambient-independent schedules whose regularity witness is selected
together with its rankwise cleaning/counting compatibility. -/
structure CorrelatedRankwiseCoarseTargetRemovalSelector
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
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
          (RankwiseSelectedCoarseTargetCompatibility
            R ξ countThreshold)

/-- Existence of one certificate-correlated selector for every positive
removal allowance. -/
def HasCorrelatedRankwiseCoarseTargetRemovalSelectors
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (CorrelatedRankwiseCoarseTargetRemovalSelector
        k r initialBound ξ)

/-! ### A concrete admissible-path formulation

The abstract selector above can be split into two independent obligations:

* an energy argument returns a certificate whose stage vector is
  `admissible`;
* the numerical counting and deletion margins hold on admissible vectors
  only.

This is the exact API needed for a coupled stopping-time construction.  The
rank-two contradiction disappears because the all-last vector need not be
admissible.
-/

/-- Stage-indexed numerical data restricted to paths which a coupled
regularity stopping-time is certified to select. -/
structure StoppingTimeRankwiseCoarseTargetRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  admissible : CoarseTargetStageIndex length → Prop
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
  certificate_admissible :
    ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
      (initial : OrderedPartitionComplex G k r),
      ∃ R : CoarseTargetOrderedComplexRegularityCertificate
          G k r initial tolerance budget length,
        admissible R.stageIndex
  densityFloor_nonneg :
    ∀ index, admissible index →
      ∀ j, 0 ≤ densityFloor index j
  defectThreshold_pos :
    ∀ index, admissible index →
      ∀ j, 0 < defectThreshold index j
  defectError_nonneg :
    ∀ index, admissible index →
      ∀ j, 0 ≤ defectError index j
  defectThreshold_le_sq :
    ∀ index, admissible index →
      ∀ j,
        defectThreshold index j ≤
          (defectError index j) ^ 2
  countThreshold_pos : 0 < countThreshold
  uniform_counting_margin :
    ∀ index : CoarseTargetStageIndex length,
      admissible index →
        countThreshold ≤
          (∏ e : PositiveOrderedFace k r,
            densityFloor index e.lowerRank) -
            (∑ e : PositiveOrderedFace k r,
              (defectError index e.lowerRank +
                tolerance e.lowerRank
                  (index e.lowerRank).1))
  uniform_deletion_margin :
    ∀ index : CoarseTargetStageIndex length,
      admissible index →
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

/-- Existence of an admissible-path schedule for every positive removal
allowance. -/
def HasStoppingTimeRankwiseCoarseTargetRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty
      (StoppingTimeRankwiseCoarseTargetRemovalSchedule
        k r initialBound ξ)

/-- An admissible-path schedule supplies the abstract correlated selector
by specializing its numerical margins to the selected admissible
certificate. -/
def correlatedSelectorOfStoppingTimeSchedule
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : StoppingTimeRankwiseCoarseTargetRemovalSchedule
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
    obtain ⟨R, hR⟩ :=
      S.certificate_admissible G initial
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
    · exact S.densityFloor_nonneg R.stageIndex hR
    · exact S.defectThreshold_pos R.stageIndex hR
    · exact S.defectError_nonneg R.stageIndex hR
    · intro j
      exact (S.tolerance_pos j (R.index j)).le
    · exact S.defectThreshold_le_sq R.stageIndex hR
    · simpa [
        CoarseTargetOrderedComplexRegularityCertificate.stageIndex,
        selectedOrderedComplexTolerance] using
        S.uniform_counting_margin R.stageIndex hR
    · intro j e
      exact
        R.coarse_upper_complexity_le_selectedUpperBound
          hinitial j e
    · exact S.uniform_deletion_margin R.stageIndex hR

/-- The former all-stage schedule is the special case in which every stage
vector is declared admissible. -/
def stoppingTimeScheduleOfRankwiseStageSchedule
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : RankwiseStageIndexedCoarseTargetRemovalSchedule
      k r initialBound ξ) :
    StoppingTimeRankwiseCoarseTargetRemovalSchedule
      k r initialBound ξ where
  tolerance := S.tolerance
  budget := S.budget
  length := S.length
  admissible := fun _ => True
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
    obtain ⟨R⟩ := S.certificate_nonempty initial
    exact ⟨R, trivial⟩
  densityFloor_nonneg := by
    intro index _hindex
    exact S.densityFloor_nonneg index
  defectThreshold_pos := by
    intro index _hindex
    exact S.defectThreshold_pos index
  defectError_nonneg := by
    intro index _hindex
    exact S.defectError_nonneg index
  defectThreshold_le_sq := by
    intro index _hindex
    exact S.defectThreshold_le_sq index
  countThreshold_pos := S.countThreshold_pos
  uniform_counting_margin := by
    intro index _hindex
    exact S.uniform_counting_margin index
  uniform_deletion_margin := by
    intro index _hindex
    exact S.uniform_deletion_margin index

/-- Every all-stage-vector schedule yields a correlated selector by
specializing its numerical data to the certificate's selected stage.
The converse fails already at rank two by
`not_hasRankwiseStageIndexedCoarseTargetRemovalSchedules_two`. -/
def correlatedSelectorOfRankwiseStageSchedule
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : RankwiseStageIndexedCoarseTargetRemovalSchedule
      k r initialBound ξ) :
    CorrelatedRankwiseCoarseTargetRemovalSelector
      k r initialBound ξ :=
    correlatedSelectorOfStoppingTimeSchedule
      (stoppingTimeScheduleOfRankwiseStageSchedule S)

/-- The corrected stopping-time-correlated selector is sufficient for
uniform ordered-pattern removal.  This is the strongest semantic endpoint
available without constructing the remaining coupled numerical selector. -/
theorem hasUniformOrderedPatternRemoval_succ_of_correlatedSelectors
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hselectors :
      HasCorrelatedRankwiseCoarseTargetRemovalSelectors
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  let S :
      CorrelatedRankwiseCoarseTargetRemovalSelector
        k (n + 1) 2 ξ :=
    Classical.choice (hselectors ξ hξ)
  refine ⟨S.countThreshold, S.countThreshold_pos, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty
    H hcount
  obtain ⟨R, ⟨C⟩⟩ :=
    S.select G (orderedPatternInitialComplex H)
      (complexity_orderedPatternInitialComplex_le_two H)
  exact
    R.removal_of_rankwiseSelectedCompatibility
      hrank H R.coarse_refines_initial C hcount

/-- Admissible-path schedule existence supplies the abstract correlated
selectors with the same ambient-independent count thresholds. -/
theorem hasCorrelatedSelectors_of_stoppingTimeSchedules
    (k r initialBound : ℕ)
    (hschedules :
      HasStoppingTimeRankwiseCoarseTargetRemovalSchedules
        k r initialBound) :
    HasCorrelatedRankwiseCoarseTargetRemovalSelectors
      k r initialBound := by
  intro ξ hξ
  obtain ⟨S⟩ := hschedules ξ hξ
  exact ⟨correlatedSelectorOfStoppingTimeSchedule S⟩

/-- A coupled admissible stopping-time construction would therefore close
uniform ordered-pattern removal without any false all-window or all-stage
premise. -/
theorem hasUniformOrderedPatternRemoval_succ_of_stoppingTimeSchedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasStoppingTimeRankwiseCoarseTargetRemovalSchedules
        k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  exact
    hasUniformOrderedPatternRemoval_succ_of_correlatedSelectors
      k n hrank
        (hasCorrelatedSelectors_of_stoppingTimeSchedules
          k (n + 1) 2 hschedules)

end Submission.GreenTao
