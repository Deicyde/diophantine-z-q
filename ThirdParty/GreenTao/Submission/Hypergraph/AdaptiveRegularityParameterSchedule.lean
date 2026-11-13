-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.AdaptiveCoarseTargetRemovalSelector
import Submission.Hypergraph.CoarseTargetRemovalScheduleBase

/-!
# Numerical limits of all-landing adaptive regularity schedules

The adaptive regularity tree removes the artificial Cartesian product of
lower-rank horizons: a lower schedule may depend on the indices selected at
all higher ranks.  The removal interface in
`AdaptiveCoarseTargetRemovalSelector`, however, asks the numerical margins
to hold on **every** root-to-leaf landing.

This file records the exact boundary of that requirement.

* At rank one the true coarse upper layer is the unchanged top layer.  The
  standard removal parameters therefore give a completely explicit adaptive
  schedule.
* At rank two, requiring the margins on every landing is still impossible.
  The root has a landing through its last index.  On that landing the
  rank-one cleaning complexity is at least the root horizon.  Cleaning and
  counting then give contradictory strict inequalities.

Thus a higher-rank parameter selector must discard nonselected branches, or
attach compatibility only to the stopping-time landing actually returned by
regularity.  Merely making the lower tree path-dependent is not enough.
-/

namespace Submission.GreenTao

open scoped BigOperators

namespace AdaptiveCoarseTargetSchedule

/-- Every admissible adaptive schedule has at least one landing, without
using an ambient regularity realization. -/
theorem landing_nonempty_of_admissible
    {k r : ℕ}
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    Nonempty S.Landing := by
  induction S with
  | nil =>
      exact ⟨Landing.nil⟩
  | @node r tolerance budget length next ih =>
      rcases hS with
        ⟨_htolerance, _hbudget, hlength, hnext⟩
      let chosen : Fin length := ⟨0, hlength⟩
      obtain ⟨lower⟩ := ih chosen (hnext chosen)
      exact ⟨Landing.node
        (tolerance := tolerance) (budget := budget)
        chosen lower⟩

/-- An admissible positive-height tree has a genuine landing through the
last index of its root horizon. -/
theorem exists_landing_root_index_eq_length_sub_one
    {k r : ℕ}
    (S : AdaptiveCoarseTargetSchedule k (r + 1))
    (hS : S.IsAdmissible) :
    ∃ P : S.Landing,
      P.index (Fin.last r) =
        P.length (Fin.last r) - 1 := by
  cases S with
  | @node _ tolerance budget length next =>
      rcases hS with
        ⟨_htolerance, _hbudget, hlength, hnext⟩
      let chosen : Fin length :=
        ⟨length - 1, by omega⟩
      obtain ⟨lower⟩ :=
        landing_nonempty_of_admissible
          (next chosen) (hnext chosen)
      let P :
          (AdaptiveCoarseTargetSchedule.node
            tolerance budget length next).Landing :=
        Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower
      refine ⟨P, ?_⟩
      simp [P, chosen]

namespace Landing

@[simp]
theorem tolerance_node_fin_one
    {k length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length →
      AdaptiveCoarseTargetSchedule k 0}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin 1) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance j =
      tolerance := by
  rw [Subsingleton.elim j (Fin.last 0)]
  exact tolerance_node_last chosen lower

@[simp]
theorem length_node_fin_one
    {k length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length →
      AdaptiveCoarseTargetSchedule k 0}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin 1) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length j =
      length := by
  rw [Subsingleton.elim j (Fin.last 0)]
  exact length_node_last chosen lower

end Landing

end AdaptiveCoarseTargetSchedule

/-! ## A constructive rank-one schedule -/

/-- At rank one the adaptive all-landing interface is inhabited by the
standard explicit removal parameters.  The root may have many possible
indices, but its tolerance is constant and the true upper cleaning
complexity is the unchanged top bound `initialBound`, so the numerical
margins are identical on every landing. -/
theorem hasAdaptiveRankwiseCoarseTargetRemovalSchedules_one
    (k initialBound : ℕ) :
    HasAdaptiveRankwiseCoarseTargetRemovalSchedules
      k 1 initialBound := by
  intro ξ hξ
  let ρ : ℝ :=
    orderedRemovalDensityFloor 1 initialBound ξ
  let η : ℝ :=
    orderedRemovalCountingError k 1 initialBound ξ
  let β0 : ℝ :=
    orderedRemovalDefectThreshold k 1 initialBound ξ
  let γ : ℝ :=
    orderedRemovalEnergyGapTarget k 1 initialBound ξ
  let tolerance : ℕ → ℝ :=
    fun _ => η
  let toleranceVector : (j : Fin 1) → ℕ → ℝ :=
    fun _ => tolerance
  let budgetVector : (j : Fin 1) → ℕ → ℕ :=
    orderedRemovalRegularityBudgetSchedule
      k 1 toleranceVector
  let budget : ℕ → ℕ :=
    budgetVector 0
  let length : ℕ :=
    orderedRemovalEnergyLength k 1 γ 0
  let schedule : AdaptiveCoarseTargetSchedule k 1 :=
    .node tolerance budget length
      (fun _ => .nil)
  let densityFloor :
      schedule.Landing → Fin 1 → ℝ :=
    fun _ _ => ρ
  let defectThreshold :
      schedule.Landing → Fin 1 → ℝ :=
    fun _ _ => β0
  let defectError :
      schedule.Landing → Fin 1 → ℝ :=
    fun _ _ => η
  let c : ℝ :=
    orderedRemovalConfigurationLowerBound
      k 1 ρ η η
  have hηpos : 0 < η :=
    orderedRemovalCountingError_pos hξ
  have hβpos : 0 < β0 :=
    orderedRemovalDefectThreshold_pos hξ
  have hγpos : 0 < γ :=
    orderedRemovalEnergyGapTarget_pos hξ
  have hlength : 0 < length := by
    exact orderedRemovalEnergyLength_pos k 1 γ 0
  have hcpos : 0 < c := by
    exact
      orderedRemovalConfigurationLowerBound_pos
        (k := k) (r := 1) (M := initialBound) hξ
  refine ⟨{
    schedule := schedule
    schedule_admissible := ?_
    densityFloor := densityFloor
    defectThreshold := defectThreshold
    defectError := defectError
    countThreshold := c
    countThreshold_pos := hcpos
    densityFloor_nonneg := ?_
    defectThreshold_pos := ?_
    defectError_nonneg := ?_
    defectThreshold_le_sq := ?_
    landing_counting_margin := ?_
    landing_deletion_margin := ?_ }⟩
  · refine ⟨?_, ?_, hlength, ?_⟩
    · intro n
      exact hηpos.le
    · intro n
      change
        (Fintype.card (OrderedFace k 1) : ℝ) <
          (budgetVector 0 n : ℝ) * η ^ 2
      exact
        orderedRemovalRegularityBudgetSchedule_spec
          (τ := toleranceVector)
          (fun (_ : Fin 1) (_ : ℕ) => hηpos)
          (0 : Fin 1) n
    · intro i
      trivial
  · intro P j
    exact (orderedRemovalDensityFloor_pos hξ).le
  · intro P j
    exact hβpos
  · intro P j
    exact hηpos.le
  · intro P j
    exact le_rfl
  · intro P
    change
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length (fun _ => .nil)).Landing at P
    cases P with
    | node chosen lower =>
        cases lower
        simp only [densityFloor, defectError,
          AdaptiveCoarseTargetSchedule.Landing.tolerance_node_fin_one,
          tolerance]
        change
          c ≤
            (∏ _e : PositiveOrderedFace k 1, ρ) -
              ∑ _e : PositiveOrderedFace k 1, (η + η)
        simp only [Finset.prod_const, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        change
          c ≤
            ρ ^ Fintype.card (PositiveOrderedFace k 1) -
              (Fintype.card (PositiveOrderedFace k 1) : ℝ) *
                (η + η)
        exact le_rfl
  · intro P
    change
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length (fun _ => .nil)).Landing at P
    cases P with
    | node chosen lower =>
        cases lower
        have hgap :
            (Fintype.card (OrderedFace k 1) : ℝ) /
                (length : ℝ) ≤
              γ := by
          have hsum :=
            (orderedRemovalEnergyLength_sum_div_lt
              (k := k) (r := 1) hγpos).le
          simpa [length, Fin.sum_univ_one] using hsum
        have harithmetic :
            (initialBound : ℝ) * ρ +
                ((Fintype.card (OrderedFace k 1) : ℝ) /
                  (length : ℝ)) / β0 ≤
              ξ := by
          have hbase :=
            orderedRemovalDeletionError_le
              (k := k) (r := 1) (M := initialBound)
              hξ hgap
          simpa [orderedRemovalDeletionError,
            orderedRemovalComplexityCoefficient,
            orderedRemovalTopSubfaceCount,
            card_orderedPositiveSubface_one,
            Nat.cast_mul] using hbase
        obtain ⟨q0, hq0⟩ :=
          Fintype.card_eq_one_iff.mp
            card_orderedPositiveSubface_one
        have huniv :
            (Finset.univ :
              Finset (OrderedPositiveSubface 1)) = {q0} := by
          ext q
          simp [hq0 q]
        rw [huniv]
        simp only [Finset.sum_singleton]
        rcases q0 with ⟨j0, f0⟩
        have hj0 : j0 = 0 := Fin.eq_zero j0
        subst j0
        simpa [schedule, densityFloor, defectThreshold,
          AdaptiveCoarseTargetSchedule.Landing.length_node_fin_one,
          CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
          length] using harithmetic

/-! ## The surviving rank-two obstruction -/

/-- The all-landing adaptive numerical interface is impossible at rank two.

The proof uses only the landing through the last root index.  Hence allowing
the lower schedule to depend on that root index does not affect the
contradiction. -/
theorem not_hasAdaptiveRankwiseCoarseTargetRemovalSchedules_two
    (k initialBound : ℕ)
    (hk : 2 ≤ k) (hinitialBound : 0 < initialBound) :
    ¬ HasAdaptiveRankwiseCoarseTargetRemovalSchedules
      k 2 initialBound := by
  intro hschedules
  obtain ⟨S⟩ := hschedules 1 (by norm_num)
  obtain ⟨P, hlast⟩ :=
    S.schedule.exists_landing_root_index_eq_length_sub_one
      S.schedule_admissible
  let index : CoarseTargetStageIndex P.length :=
    P.stageIndex
  let upper : Fin 2 → ℕ :=
    fun j =>
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound
        2 initialBound P.budget P.length index j
  let ρ : Fin 2 → ℝ :=
    S.densityFloor P
  let β : Fin 2 → ℝ :=
    S.defectThreshold P
  let δ : Fin 2 → ℝ :=
    S.defectError P
  let cleaningTerm : OrderedPositiveSubface 2 → ℝ :=
    fun q =>
      (upper q.1 : ℝ) * ρ q.1 +
        ((Fintype.card
            (OrderedFace k (q.1.1 + 1)) : ℝ) /
              (P.length q.1 : ℝ)) /
          β q.1
  let product : ℝ :=
    ∏ e : PositiveOrderedFace k 2, ρ e.lowerRank
  let errorSum : ℝ :=
    ∑ e : PositiveOrderedFace k 2,
      (δ e.lowerRank +
        P.tolerance e.lowerRank
          (P.index e.lowerRank))
  let q0 : OrderedPositiveSubface 2 :=
    ⟨0, Fin.castLEOrderEmb (by omega)⟩
  let q1 : OrderedPositiveSubface 2 :=
    ⟨1, Fin.castLEOrderEmb (by omega)⟩
  let e0 : PositiveOrderedFace k 2 :=
    ⟨0, Fin.castLEOrderEmb (by omega)⟩
  let e1 : PositiveOrderedFace k 2 :=
    ⟨1, Fin.castLEOrderEmb hk⟩
  have hlengthPos : ∀ j, 0 < P.length j :=
    P.length_pos S.schedule_admissible
  have hbudgetSpec :
      ∀ j n,
        (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) <
          (P.budget j n : ℝ) *
            (P.tolerance j n) ^ 2 :=
    P.budget_spec S.schedule_admissible
  have htoleranceNonneg :
      ∀ j n, 0 ≤ P.tolerance j n :=
    P.tolerance_nonneg S.schedule_admissible
  have hbudget1 : ∀ n, 0 < P.budget 1 n := by
    intro n
    by_contra hnot
    have hzero : P.budget 1 n = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hspec := hbudgetSpec (1 : Fin 2) n
    rw [hzero] at hspec
    norm_num at hspec
    exact
      (not_lt_of_ge
        (Nat.cast_nonneg
          (Fintype.card (OrderedFace k 2)))) hspec
  have hlengthUpper : P.length 1 ≤ upper 0 := by
    have hlast' :
        P.index (1 : Fin 2) =
          P.length (1 : Fin 2) - 1 := by
      simpa using hlast
    have hfactor :=
      succ_le_fixedUpperLayerComplexityFactor
        1 (P.budget 1) hbudget1 (P.length 1 - 1)
    have hfactor' :
        P.length 1 ≤
          fixedUpperLayerComplexityFactor
            1 (P.budget 1) (P.index 1) := by
      rw [hlast']
      have hsub : P.length 1 - 1 + 1 = P.length 1 := by
        have := hlengthPos 1
        omega
      simpa [hsub] using hfactor
    unfold upper
    rw [
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
      dif_pos (by omega)]
    change
      P.length 1 ≤
        initialBound *
          fixedUpperLayerComplexityFactor
            1 (P.budget 1) (P.index 1)
    exact hfactor'.trans
      (Nat.le_mul_of_pos_left _ hinitialBound)
  have hupperPos : ∀ j, 0 < upper j := by
    intro j
    unfold upper
    by_cases hj : j.1 + 1 < 2
    · rw [
        CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
        dif_pos hj]
      exact Nat.mul_pos hinitialBound
        (fixedUpperLayerComplexityFactor_pos _ _ _)
    · rw [
        CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
        dif_neg hj]
      exact hinitialBound
  have hρnonneg : ∀ j, 0 ≤ ρ j := by
    intro j
    exact S.densityFloor_nonneg P j
  have hβpos : ∀ j, 0 < β j := by
    intro j
    exact S.defectThreshold_pos P j
  have hδnonneg : ∀ j, 0 ≤ δ j := by
    intro j
    exact S.defectError_nonneg P j
  have hcleaningTerm_nonneg :
      ∀ q, 0 ≤ cleaningTerm q := by
    intro q
    apply add_nonneg
    · exact mul_nonneg (by positivity) (hρnonneg q.1)
    · exact div_nonneg
        (div_nonneg (by positivity)
          (by
            exact_mod_cast (hlengthPos q.1).le))
        (hβpos q.1).le
  have hdeletion :
      (∑ q : OrderedPositiveSubface 2,
          cleaningTerm q) ≤ 1 := by
    simpa [cleaningTerm, upper, ρ, β, index] using
      S.landing_deletion_margin P
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
                exact_mod_cast (hlengthPos q.1).le))
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
  have hcount := S.landing_counting_margin P
  have herror_lt_product : errorSum < product := by
    dsimp only [errorSum, product, ρ, δ] at hcount ⊢
    linarith [S.countThreshold_pos]
  have herrorTerm_nonneg :
      ∀ e : PositiveOrderedFace k 2,
        0 ≤
          δ e.lowerRank +
            P.tolerance e.lowerRank
              (P.index e.lowerRank) := by
    intro e
    exact add_nonneg (hδnonneg e.lowerRank)
      (htoleranceNonneg _ _)
  have hδ1_lt_product : δ 1 < product := by
    have hsingle :
        δ e1.lowerRank +
              P.tolerance e1.lowerRank
                (P.index e1.lowerRank) ≤
            errorSum := by
      exact Finset.single_le_sum
        (fun e _ => herrorTerm_nonneg e)
        (Finset.mem_univ e1)
    have hδle :
        δ 1 ≤
          δ e1.lowerRank +
            P.tolerance e1.lowerRank
              (P.index e1.lowerRank) := by
      calc
        δ 1 = δ e1.lowerRank := by simp [e1]
        _ ≤
            δ e1.lowerRank +
              P.tolerance e1.lowerRank
                (P.index e1.lowerRank) :=
          le_add_of_nonneg_right
            (htoleranceNonneg _ _)
    exact (hδle.trans hsingle).trans_lt
      herror_lt_product
  have hδ1pos : 0 < δ 1 := by
    have hβδ :=
      S.defectThreshold_le_sq P (1 : Fin 2)
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
      (S.defectThreshold_le_sq P (1 : Fin 2)).trans_lt
        ((sq_lt_sq₀ (hδnonneg 1) (hρ0pos.le)).2
          hδrho)
  have hgap1_le :
      ((Fintype.card (OrderedFace k 2) : ℝ) /
          (P.length 1 : ℝ)) / β 1 ≤ 1 := by
    have hleftNonneg :
        0 ≤ (upper q1.1 : ℝ) * ρ q1.1 :=
      mul_nonneg (by positivity) (hρnonneg q1.1)
    calc
      ((Fintype.card (OrderedFace k 2) : ℝ) /
            (P.length 1 : ℝ)) /
          β 1 ≤
          (upper q1.1 : ℝ) * ρ q1.1 +
            ((Fintype.card (OrderedFace k 2) : ℝ) /
                (P.length 1 : ℝ)) /
              β 1 :=
        le_add_of_nonneg_left hleftNonneg
      _ = cleaningTerm q1 := by
        simp [cleaningTerm, q1]
      _ ≤ 1 := hterm_le q1
  have hfacePos :
      0 < Fintype.card (OrderedFace k 2) :=
    card_orderedFace_pos_of_le hk
  have hlengthPosReal : (0 : ℝ) < P.length 1 := by
    exact_mod_cast hlengthPos 1
  have hface_le_lengthBeta :
      (Fintype.card (OrderedFace k 2) : ℝ) ≤
        (P.length 1 : ℝ) * β 1 := by
    have hdiv_le_beta :
        (Fintype.card (OrderedFace k 2) : ℝ) /
            (P.length 1 : ℝ) ≤
          β 1 := by
      have := (div_le_iff₀ (hβpos 1)).1 hgap1_le
      simpa using this
    simpa [mul_comm] using
      (div_le_iff₀ hlengthPosReal).1 hdiv_le_beta
  have hone_lt_lengthRho :
      (1 : ℝ) <
        (P.length 1 : ℝ) * (ρ 0) ^ 2 := by
    have hfaceOne :
        (1 : ℝ) ≤
          (Fintype.card (OrderedFace k 2) : ℝ) := by
      exact_mod_cast hfacePos
    have hstrict :
        (P.length 1 : ℝ) * β 1 <
          (P.length 1 : ℝ) * (ρ 0) ^ 2 :=
      mul_lt_mul_of_pos_left hβrho hlengthPosReal
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
      (P.length 1 : ℝ) ≤ (upper 0 : ℝ) := by
    exact_mod_cast hlengthUpper
  have hlengthRho_le :
      (P.length 1 : ℝ) * (ρ 0) ^ 2 ≤ 1 := by
    exact
      (mul_le_mul_of_nonneg_right
        hlengthUpperCast (sq_nonneg (ρ 0))).trans
          hupperRhoSq'
  exact (not_lt_of_ge hlengthRho_le)
    hone_lt_lengthRho

end Submission.GreenTao
