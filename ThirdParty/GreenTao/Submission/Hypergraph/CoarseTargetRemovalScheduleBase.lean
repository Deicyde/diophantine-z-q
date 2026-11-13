import Submission.Hypergraph.CoarseTargetRemovalSchedules
import Submission.Hypergraph.CoarseTargetRankwiseRemovalBridge

/-!
# Base cases for stage-indexed coarse-target removal schedules

This file settles the stage-indexed selector at rank zero and records the
exact rank-one obstruction caused by charging the generic lower-layer tower
bound to the unchanged top layer.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Rank zero -/

/-- At rank zero there are no selected stages, no positive faces, and no
energy gaps.  Consequently every positive removal allowance admits the same
constant numerical schedule. -/
theorem hasStageIndexedCoarseTargetRemovalSchedules_zero
    (k initialBound : ℕ) :
    HasStageIndexedCoarseTargetRemovalSchedules
      k 0 initialBound := by
  intro ξ hξ
  let tolerance : (j : Fin 0) → ℕ → ℝ :=
    fun j => Fin.elim0 j
  let budget : (j : Fin 0) → ℕ → ℕ :=
    fun j => Fin.elim0 j
  let length : Fin 0 → ℕ :=
    fun j => Fin.elim0 j
  let densityFloor : CoarseTargetStageIndex length → ℝ :=
    fun _ => 1
  let defectThreshold : CoarseTargetStageIndex length → ℝ :=
    fun _ => 1
  let defectError : CoarseTargetStageIndex length → ℝ :=
    fun _ => 1
  refine ⟨{
    tolerance := tolerance
    budget := budget
    length := length
    densityFloor := densityFloor
    defectThreshold := defectThreshold
    defectError := defectError
    countThreshold := 1 / 2
    tolerance_pos := ?_
    budget_spec := ?_
    length_pos := ?_
    densityFloor_nonneg := ?_
    defectThreshold_pos := ?_
    defectError_nonneg := ?_
    defectThreshold_le_sq := ?_
    countThreshold_pos := ?_
    uniform_counting_margin := ?_
    uniform_deletion_margin := ?_ }⟩
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j
  · intro index
    norm_num [densityFloor]
  · intro index
    norm_num [defectThreshold]
  · intro index
    norm_num [defectError]
  · intro index
    norm_num [defectThreshold, defectError]
  · norm_num
  · intro index
    have hfaces :
        (Finset.univ :
          Finset (PositiveOrderedFace k 0)) = ∅ := by
      ext e
      exact Fin.elim0 e.lowerRank
    norm_num [hfaces]
  · intro index
    simpa [coarseTargetSelectedCoarseComplexityBound] using hξ.le

/-! ## Exact rank-one complexity facts -/

/-- Every partition of the arity-zero face space has exactly one atom. -/
theorem facePartition_complexity_fin_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    (P : FacePartition (Fin 0 → G)) :
    P.complexity = 1 := by
  letI : Nonempty (Fin 0 → G) :=
    ⟨fun i => Fin.elim0 i⟩
  have hpos : 0 < P.complexity := by
    unfold FacePartition.complexity
    exact (P.parts_nonempty (by simp)).card_pos
  have hle := P.complexity_le_card
  have hcard : Fintype.card (Fin 0 → G) = 1 := by
    simp
  omega

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- At rank one the only upper layer used by cleaning is the unchanged top
layer.  Its complexity is therefore bounded by the initial top-layer bound,
independently of the selected lower-layer tower index. -/
theorem rank_one_coarse_upper_complexity_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k initialBound : ℕ}
    {initial : OrderedPartitionComplex G k 1}
    {ε : (j : Fin 1) → ℕ → ℝ}
    {budget : (j : Fin 1) → ℕ → ℕ}
    {length : Fin 1 → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k 1 initial ε budget length)
    (hinitial :
      ∀ e : OrderedFace k 1,
        FacePartition.complexity
          (initial.topLayer e) ≤ initialBound) :
    ∀ e : OrderedFace k 1,
      FacePartition.complexity
        (R.coarse.topLayer e) ≤ initialBound := by
  intro e
  rw [R.coarse_topLayer_eq]
  exact hinitial e

/-- Dependent-index form of
`rank_one_coarse_upper_complexity_le`, matching the rankwise cleaning API. -/
theorem rank_one_coarse_partition_succ_complexity_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k initialBound : ℕ}
    {initial : OrderedPartitionComplex G k 1}
    {ε : (j : Fin 1) → ℕ → ℝ}
    {budget : (j : Fin 1) → ℕ → ℕ}
    {length : Fin 1 → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k 1 initial ε budget length)
    (hinitial :
      ∀ e : OrderedFace k 1,
        FacePartition.complexity
          (initial.topLayer e) ≤ initialBound) :
    ∀ (j : Fin 1) (e : OrderedFace k (j.1 + 1)),
      FacePartition.complexity
        (R.coarse.partition j.succ e) ≤ initialBound := by
  intro j
  refine Fin.cases ?_ (fun i => Fin.elim0 i) j
  intro e
  convert
    R.rank_one_coarse_upper_complexity_le hinitial e using 1
  rfl

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## The generic-bound obstruction at rank one -/

/-- The last admissible vector of stage indices. -/
def lastCoarseTargetStageIndex
    {r : ℕ} {length : Fin r → ℕ}
    (hlength : ∀ j, 0 < length j) :
    CoarseTargetStageIndex length :=
  fun j =>
    ⟨length j - 1, by
      have := hlength j
      omega⟩

/-- If every rank-zero tower step has a positive budget, its generic
complexity factor after `n` steps is at least `n + 1`. -/
theorem succ_le_fixedUpperLayerComplexityFactor_zero
    (budget : ℕ → ℕ)
    (hbudget : ∀ n, 0 < budget n) :
    ∀ n,
      n + 1 ≤ fixedUpperLayerComplexityFactor 0 budget n := by
  intro n
  induction n with
  | zero =>
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      rw [fixedUpperLayerComplexityFactor]
      have hpow :
          2 ≤ (2 : ℕ) ^ budget n := by
        simpa using
          Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ))
            (hbudget n)
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤
            (2 : ℕ) ^ budget n *
              fixedUpperLayerComplexityFactor 0 budget n :=
          Nat.mul_le_mul hpow ih
        _ =
            (2 ^ (0 + 1)) ^ budget n *
              fixedUpperLayerComplexityFactor 0 budget n := by
          norm_num

/-- At the last rank-one stage, the generic selected-complexity bound is at
least the schedule length.  This is precisely the artificial feedback absent
from the actual rank-one upper layer. -/
theorem length_le_coarseTargetSelectedCoarseComplexityBound_one_last
    {initialBound : ℕ}
    (budget : (j : Fin 1) → ℕ → ℕ)
    (length : Fin 1 → ℕ)
    (hinitialBound : 0 < initialBound)
    (hlength : ∀ j, 0 < length j)
    (hbudget : ∀ j n, 0 < budget j n) :
    length 0 ≤
      coarseTargetSelectedCoarseComplexityBound
        1 initialBound budget length
          (lastCoarseTargetStageIndex hlength) := by
  have hfactor :=
    succ_le_fixedUpperLayerComplexityFactor_zero
      (budget 0) (hbudget 0) (length 0 - 1)
  have hsub : length 0 - 1 + 1 = length 0 := by
    have hlength0 := hlength 0
    omega
  have hfactor' :
      length 0 ≤
        fixedUpperLayerComplexityFactor
          0 (budget 0) (length 0 - 1) := by
    simpa [hsub] using hfactor
  unfold coarseTargetSelectedCoarseComplexityBound
  rw [Fin.sum_univ_one]
  change
    length 0 ≤
      initialBound *
        (1 +
          fixedUpperLayerComplexityFactor
            0 (budget 0) (length 0 - 1))
  calc
    length 0 ≤
        fixedUpperLayerComplexityFactor
          0 (budget 0) (length 0 - 1) :=
      hfactor'
    _ ≤
        1 *
          (1 +
            fixedUpperLayerComplexityFactor
              0 (budget 0) (length 0 - 1)) := by
      simp
    _ ≤
        initialBound *
          (1 +
            fixedUpperLayerComplexityFactor
              0 (budget 0) (length 0 - 1)) := by
      exact Nat.mul_le_mul_right _
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt hinitialBound))

/-- A rank-one ordered face exists as soon as the ambient configuration has
at least one vertex class. -/
theorem card_orderedFace_one_pos
    {k : ℕ} (hk : 1 ≤ k) :
    0 < Fintype.card (OrderedFace k 1) := by
  exact Fintype.card_pos_iff.mpr
    ⟨Fin.castLEOrderEmb hk⟩

/-- Hence a rank-one complex has at least one positive configuration face. -/
theorem card_positiveOrderedFace_one_pos
    {k : ℕ} (hk : 1 ≤ k) :
    0 < Fintype.card (PositiveOrderedFace k 1) := by
  exact Fintype.card_pos_iff.mpr
    ⟨⟨0, Fin.castLEOrderEmb hk⟩⟩

/-- A rank-one top face has a positive subface. -/
theorem card_orderedPositiveSubface_one_pos :
    0 < Fintype.card (OrderedPositiveSubface 1) := by
  exact Fintype.card_pos_iff.mpr
    ⟨⟨0, Fin.castLEOrderEmb (by omega)⟩⟩

/-- A rank-one face has exactly one positive subface. -/
theorem card_orderedPositiveSubface_one :
    Fintype.card (OrderedPositiveSubface 1) = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  let q0 : OrderedPositiveSubface 1 :=
    ⟨0, Fin.castLEOrderEmb (by omega)⟩
  refine ⟨q0, ?_⟩
  intro q
  rcases q with ⟨j, e⟩
  have hj : j = 0 := Fin.eq_zero j
  subst j
  apply PSigma.ext
  · rfl
  · apply heq_of_eq
    apply DFunLike.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- A positive power of a number in `[0,1]` is at most the number itself. -/
theorem pow_le_self_of_nonneg_of_le_one
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    x ^ n ≤ x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hn)
  rw [pow_succ]
  simpa using
    mul_le_mul_of_nonneg_right
      (pow_le_one₀ hx0 hx1) hx0

/-- The present generic-bound schedule interface has no rank-one inhabitant
when both the ambient rank and the initial complexity bound are positive.

The contradiction already occurs at removal allowance `1`.  At the last
allowed tower index the generic factor is at least the schedule length.
Cleaning forces `B * ρ ≤ 1`, while reciprocal-gap control and counting force
`1 < length * ρ²`.  Since `length ≤ B` and `B ≥ 1`, these inequalities are
incompatible.

This is an obstruction to the *interface*, not to rank-one removal: the
preceding exact lemma shows that the actual upper layer used in cleaning has
the fixed initial complexity, independent of this tower factor. -/
theorem not_hasStageIndexedCoarseTargetRemovalSchedules_one
    (k initialBound : ℕ)
    (hk : 1 ≤ k) (hinitialBound : 0 < initialBound) :
    ¬ HasStageIndexedCoarseTargetRemovalSchedules
      k 1 initialBound := by
  intro hschedules
  obtain ⟨S⟩ := hschedules 1 (by norm_num)
  let index : CoarseTargetStageIndex S.length :=
    lastCoarseTargetStageIndex S.length_pos
  let ρ : ℝ := S.densityFloor index
  let β : ℝ := S.defectThreshold index
  let δ : ℝ := S.defectError index
  let L : ℕ := S.length 0
  let B : ℕ :=
    coarseTargetSelectedCoarseComplexityBound
      1 initialBound S.budget S.length index
  let A : ℕ := Fintype.card (OrderedFace k 1)
  let N : ℕ := Fintype.card (PositiveOrderedFace k 1)
  let C : ℕ := Fintype.card (OrderedPositiveSubface 1)
  have hLpos : 0 < L := by
    exact S.length_pos 0
  have hApos : 0 < A := by
    exact card_orderedFace_one_pos hk
  have hNpos : 0 < N := by
    exact card_positiveOrderedFace_one_pos hk
  have hCpos : 0 < C := by
    exact card_orderedPositiveSubface_one_pos
  have hbudget : ∀ j n, 0 < S.budget j n := by
    intro j n
    have hspec := S.budget_spec j n
    have hj : j = 0 := Fin.eq_zero j
    subst j
    by_contra hnot
    have hzero : S.budget 0 n = 0 :=
      Nat.eq_zero_of_not_pos hnot
    norm_num [hzero] at hspec
    have hcard_nonneg :
        (0 : ℝ) ≤
          (Fintype.card (OrderedFace k 1) : ℝ) := by
      positivity
    exact (not_lt_of_ge hcard_nonneg) hspec
  have hLB : L ≤ B := by
    exact
      length_le_coarseTargetSelectedCoarseComplexityBound_one_last
        S.budget S.length hinitialBound S.length_pos hbudget
  have hBpos : 0 < B :=
    lt_of_lt_of_le hLpos hLB
  have hρnonneg : 0 ≤ ρ :=
    S.densityFloor_nonneg index
  have hβpos : 0 < β :=
    S.defectThreshold_pos index
  have hδnonneg : 0 ≤ δ :=
    S.defectError_nonneg index
  have hβδ : β ≤ δ ^ 2 :=
    S.defectThreshold_le_sq index
  have hcount :=
    S.uniform_counting_margin index
  have hsum_lt_prod :
      (∑ e : PositiveOrderedFace k 1,
          (δ +
            S.tolerance e.lowerRank
              (index e.lowerRank).1)) <
        ∏ _e : PositiveOrderedFace k 1, ρ := by
    linarith [S.countThreshold_pos]
  let e0 : PositiveOrderedFace k 1 :=
    ⟨0, Fin.castLEOrderEmb hk⟩
  have hterm_nonneg :
      ∀ e : PositiveOrderedFace k 1,
        0 ≤
          δ +
            S.tolerance e.lowerRank
              (index e.lowerRank).1 := by
    intro e
    exact add_nonneg hδnonneg
      (S.tolerance_pos _ _).le
  have hterm_le_sum :
      δ +
          S.tolerance e0.lowerRank
            (index e0.lowerRank).1 ≤
        ∑ e : PositiveOrderedFace k 1,
          (δ +
            S.tolerance e.lowerRank
              (index e.lowerRank).1) := by
    exact Finset.single_le_sum
      (fun e _ => hterm_nonneg e)
      (Finset.mem_univ e0)
  have hδ_lt_prod :
      δ < ∏ _e : PositiveOrderedFace k 1, ρ := by
    exact lt_of_le_of_lt
      ((le_add_of_nonneg_right
        (S.tolerance_pos e0.lowerRank
          (index e0.lowerRank).1).le).trans
        hterm_le_sum)
      hsum_lt_prod
  have hδpos : 0 < δ := by
    have hδsqpos : 0 < δ ^ 2 :=
      lt_of_lt_of_le hβpos hβδ
    nlinarith
  have hprodpos :
      0 < ∏ _e : PositiveOrderedFace k 1, ρ :=
    hδpos.trans hδ_lt_prod
  have hprod_eq :
      (∏ _e : PositiveOrderedFace k 1, ρ) = ρ ^ N := by
    simp [N]
  have hρpos : 0 < ρ := by
    by_contra hnot
    have hρzero : ρ = 0 :=
      le_antisymm (not_lt.mp hnot) hρnonneg
    rw [hprod_eq, hρzero] at hprodpos
    simp [Nat.ne_of_gt hNpos] at hprodpos
  have hgap_nonneg :
      0 ≤
        (∑ j : Fin 1,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (S.length j : ℝ)) / β := by
    apply div_nonneg
    · exact Finset.sum_nonneg
        (fun j _ => div_nonneg (by positivity) (by positivity))
    · exact hβpos.le
  have hdeletion :=
    S.uniform_deletion_margin index
  have hfirst_le :
      (C : ℝ) * (B : ℝ) * ρ ≤ 1 := by
    dsimp only [C, B, ρ, β, L, index] at hdeletion ⊢
    linarith
  have hCcast : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hCpos
  have hBrho_nonneg :
      0 ≤ (B : ℝ) * ρ :=
    mul_nonneg (by positivity) hρnonneg
  have hBrho_le : (B : ℝ) * ρ ≤ 1 := by
    calc
      (B : ℝ) * ρ =
          1 * ((B : ℝ) * ρ) := by ring
      _ ≤ (C : ℝ) * ((B : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_right hCcast hBrho_nonneg
      _ = (C : ℝ) * (B : ℝ) * ρ := by ring
      _ ≤ 1 := hfirst_le
  have hBcast : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hBpos
  have hρle : ρ ≤ 1 := by
    calc
      ρ = 1 * ρ := by ring
      _ ≤ (B : ℝ) * ρ :=
        mul_le_mul_of_nonneg_right hBcast hρnonneg
      _ ≤ 1 := hBrho_le
  have hprod_le_rho :
      (∏ _e : PositiveOrderedFace k 1, ρ) ≤ ρ := by
    rw [hprod_eq]
    exact pow_le_self_of_nonneg_of_le_one
      hρnonneg hρle hNpos
  have hδrho : δ < ρ :=
    hδ_lt_prod.trans_le hprod_le_rho
  have hβrho : β < ρ ^ 2 := by
    apply hβδ.trans_lt
    exact
      (sq_lt_sq₀ hδnonneg hρpos.le).2 hδrho
  have hgap_le :
      (∑ j : Fin 1,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (S.length j : ℝ)) / β ≤ 1 := by
    have hfirst_nonneg :
        0 ≤
          (Fintype.card (OrderedPositiveSubface 1) : ℝ) *
            (coarseTargetSelectedCoarseComplexityBound
              1 initialBound S.budget S.length index : ℝ) *
            S.densityFloor index := by
      positivity
    linarith [hdeletion]
  have hAdivLdivβ :
      ((A : ℝ) / (L : ℝ)) / β ≤ 1 := by
    simpa [A, L, Fin.sum_univ_one] using hgap_le
  have hLcast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLpos
  have hA_le_Lbeta :
      (A : ℝ) ≤ (L : ℝ) * β := by
    have hAdivL_le_beta :
        (A : ℝ) / (L : ℝ) ≤ β := by
      have :=
        (div_le_iff₀ hβpos).1 hAdivLdivβ
      simpa using this
    have :=
      (div_le_iff₀ hLcast).1 hAdivL_le_beta
    nlinarith
  have hAcast : (1 : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hApos
  have hone_lt_Lrho :
      (1 : ℝ) < (L : ℝ) * ρ ^ 2 := by
    have hLbeta_lt :
        (L : ℝ) * β < (L : ℝ) * ρ ^ 2 :=
      mul_lt_mul_of_pos_left hβrho hLcast
    exact
      (hAcast.trans hA_le_Lbeta).trans_lt hLbeta_lt
  have hBrho_sq_le :
      ((B : ℝ) * ρ) ^ 2 ≤ 1 := by
    simpa using
      (sq_le_sq₀ hBrho_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
        hBrho_le
  have hB_le_Bsq :
      (B : ℝ) ≤ (B : ℝ) ^ 2 := by
    calc
      (B : ℝ) = (B : ℝ) * 1 := by ring
      _ ≤ (B : ℝ) * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hBcast (by positivity)
      _ = (B : ℝ) ^ 2 := by ring
  have hB_rhosq_le :
      (B : ℝ) * ρ ^ 2 ≤ 1 := by
    calc
      (B : ℝ) * ρ ^ 2 ≤
          (B : ℝ) ^ 2 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_right hB_le_Bsq (sq_nonneg ρ)
      _ = ((B : ℝ) * ρ) ^ 2 := by ring
      _ ≤ 1 := hBrho_sq_le
  have hLBcast : (L : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hLB
  have hL_rhosq_le :
      (L : ℝ) * ρ ^ 2 ≤ 1 := by
    exact
      (mul_le_mul_of_nonneg_right hLBcast
        (sq_nonneg ρ)).trans hB_rhosq_le
  exact (not_lt_of_ge hL_rhosq_le) hone_lt_Lrho

/-! ## Rank one with the exact upper-rank bound -/

/-- Although the generic global-bound schedule is impossible at rank one,
the rankwise coarse-target bridge closes with an explicit constant numerical
schedule.  The regularity tolerance and defect parameters are computed from
the true top-layer bound `2`; the energy-selection length is then chosen by a
single ceiling, with no feedback through the arity-zero tower complexity. -/
theorem hasUniformOrderedPatternRemoval_one_rankwise
    (k : ℕ) (hk : 1 ≤ k) :
    HasUniformOrderedPatternRemoval k 1 := by
  intro ξ hξ
  let ρ : ℝ :=
    orderedRemovalDensityFloor 1 2 ξ
  let η : ℝ :=
    orderedRemovalCountingError k 1 2 ξ
  let β0 : ℝ :=
    orderedRemovalDefectThreshold k 1 2 ξ
  let γ : ℝ :=
    orderedRemovalEnergyGapTarget k 1 2 ξ
  let tolerance : (j : Fin 1) → ℕ → ℝ :=
    fun _ _ => η
  let budget : (j : Fin 1) → ℕ → ℕ :=
    orderedRemovalRegularityBudgetSchedule k 1 tolerance
  let length : Fin 1 → ℕ :=
    orderedRemovalEnergyLength k 1 γ
  let c : ℝ :=
    orderedRemovalConfigurationLowerBound k 1 ρ η η
  have hηpos : 0 < η := by
    exact orderedRemovalCountingError_pos hξ
  have hβpos : 0 < β0 := by
    exact orderedRemovalDefectThreshold_pos hξ
  have hγpos : 0 < γ := by
    exact orderedRemovalEnergyGapTarget_pos hξ
  have hcpos : 0 < c := by
    exact
      orderedRemovalConfigurationLowerBound_pos
        (k := k) (r := 1) (M := 2) hξ
  refine ⟨c, hcpos, ?_⟩
  intro G instFintype instDecidableEq instNonempty H hcount
  let initial : OrderedPartitionComplex G k 1 :=
    orderedPatternInitialComplex H
  obtain ⟨R⟩ :=
    CoarseTargetOrderedComplexRegularityCertificate.nonempty
      initial tolerance budget length
      (fun _ _ => hηpos.le)
      (by
        intro j n
        exact
          orderedRemovalRegularityBudgetSchedule_spec
            (fun _ _ => hηpos) j n)
      (orderedRemovalEnergyLength_pos k 1 γ)
  let α : ℕ → ℝ := fun _ => ρ
  let β : ℕ → ℝ := fun _ => β0
  let δ : ℕ → ℝ := fun _ => η
  let τ : OrderedRegularityTolerance 1 :=
    selectedOrderedComplexTolerance tolerance R.index
  let D : OrderedPattern.DeletionFamily
      (G := G) k 1 :=
    R.toCoarseFine.orderedCoarseBadBaseDeletionFamily α β
  have hcount' :
      H.toWeighted.patternCount <
        (∏ e : PositiveOrderedFace k 1, α e.rank) -
          (∑ e : PositiveOrderedFace k 1,
            (δ e.rank + τ e.lowerRank)) := by
    simpa [c, orderedRemovalConfigurationLowerBound,
      orderedRemovalConfigurationFaceCount, α, δ, τ,
      selectedOrderedComplexTolerance, tolerance,
      mul_add] using hcount
  have hcover : H.IsCover D := by
    apply orderedCoarseBadBaseDeletionFamily_isCover_rankwise
      hk H R.toCoarseFine R.coarse_refines_initial
      α β τ R.isFullyMixedPreliminaryOrderedRegular δ
    · intro m
      exact (orderedRemovalDensityFloor_pos hξ).le
    · intro j
      exact hηpos.le
    · intro m
      exact hηpos.le
    · intro m
      exact hβpos.le
    · intro m
      exact le_rfl
    · exact hcount'
  refine ⟨D, hcover, ?_⟩
  intro e
  let upperBound : Fin 1 → ℕ :=
    CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
      1 2 budget length R.stageIndex
  have hinitial :
      ∀ (j : Fin 2) (f : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j f) ≤ 2 := by
    exact complexity_orderedPatternInitialComplex_le_two H
  have hcoarse :
      ∀ (j : Fin 1) (f : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (R.coarse.partition j.succ f) ≤ upperBound j := by
    intro j f
    simpa [upperBound] using
      R.coarse_upper_complexity_le_selectedUpperBound
        hinitial j f
  have hdeletion :=
    R.faceDeletionDensity_orderedCoarseBadBase_rankwise_le
      upperBound hcoarse α β
      (fun _ => (orderedRemovalDensityFloor_pos hξ).le)
      (fun _ => hβpos) e
  obtain ⟨q0, hq0⟩ :=
    Fintype.card_eq_one_iff.mp
      card_orderedPositiveSubface_one
  have huniv :
      (Finset.univ :
        Finset (OrderedPositiveSubface 1)) = {q0} := by
    ext q
    simp [hq0 q]
  rcases q0 with ⟨j0, f0⟩
  have hj0 : j0 = 0 := Fin.eq_zero j0
  subst j0
  have hgap :
      (Fintype.card (OrderedFace k 1) : ℝ) /
          (length 0 : ℝ) ≤ γ := by
    have hsum :=
      (orderedRemovalEnergyLength_sum_div_lt
        (k := k) (r := 1) hγpos).le
    simpa [length, Fin.sum_univ_one] using hsum
  have harithmetic :
      (2 : ℝ) * ρ +
          ((Fintype.card (OrderedFace k 1) : ℝ) /
            (length 0 : ℝ)) / β0 ≤
        ξ := by
    have hbase :=
      orderedRemovalDeletionError_le
        (k := k) (r := 1) (M := 2)
        hξ hgap
    simpa [orderedRemovalDeletionError,
      orderedRemovalComplexityCoefficient,
      orderedRemovalTopSubfaceCount,
      card_orderedPositiveSubface_one,
      ρ, β0] using hbase
  apply hdeletion.trans
  rw [huniv]
  simp only [Finset.sum_singleton]
  simpa [upperBound,
    CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
    α, β, ρ, β0, length] using harithmetic

end Submission.GreenTao
