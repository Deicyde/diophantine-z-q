import Submission.Hypergraph.RankPrefixRemovalSelector

/-!
# Weighted extensions of the rank-prefix removal selector

This file develops the concrete weighted energy mechanism needed by the
correlated rank-prefix selector.  A positive defect threshold can be held
constant over a finite block; taking the block long enough makes its
cumulative weight pay the complete fixed-upper energy budget.  The weighted
stopping theorem then returns a literal selected gap divided by that defect
threshold.

The rank-zero removal-margin extension is constructed unconditionally.  The
later sections isolate the additional block-stability data needed to iterate
the construction top-down without replacing selected gaps by reciprocal
horizons or requiring inequalities at unselected landings.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Constant-weight cumulative energy blocks -/

/-- The standard energy horizon for the literal-gap allowance `share * β`.
It is positive for every input; positivity of the allowance is used only
when proving that its cumulative weight pays the energy budget. -/
noncomputable def rankPrefixWeightedEnergyLength
    (k j : ℕ) (share β : ℝ) : ℕ :=
  growthRegularityLength k j (share * β)

theorem rankPrefixWeightedEnergyLength_pos
    (k j : ℕ) (share β : ℝ) :
    0 < rankPrefixWeightedEnergyLength k j share β :=
  growthRegularityLength_pos k j (share * β)

/-- A block with constant positive weight `β` and the ceiling horizon above
has enough cumulative weighted allowance to pay the complete fixed-upper
rank-`j` energy budget. -/
theorem orderedFace_card_le_sum_rankPrefixWeightedEnergyLength
    {k j : ℕ} {share β : ℝ}
    (hshare : 0 < share) (hβ : 0 < β) :
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) ≤
      ∑ _i ∈ Finset.range
          (rankPrefixWeightedEnergyLength k j share β),
        share * β := by
  let L : ℕ :=
    rankPrefixWeightedEnergyLength k j share β
  have hL : 0 < L :=
    rankPrefixWeightedEnergyLength_pos k j share β
  have hLcast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hL
  have hdiv :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
          (L : ℝ) <
        share * β := by
    simpa [L, rankPrefixWeightedEnergyLength] using
      (orderedFace_card_div_growthRegularityLength_lt
        (mul_pos hshare hβ))
  have hmul :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (L : ℝ) * (share * β) :=
    by
      simpa [mul_comm] using
        (div_lt_iff₀ hLcast).1 hdiv
  simpa only [Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] using hmul.le

/-- Constant-weight specialization of the weighted fixed-upper selector.
It returns a selected literal gap satisfying `gap / β ≤ share`. -/
theorem exists_weightedFixedUpperLayerCoarseFine_const
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (tolerance : ℕ → ℝ) (budget : ℕ → ℕ)
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    {share β : ℝ}
    (hshare : 0 < share) (hβ : 0 < β) :
    Nonempty
      (WeightedFixedUpperLayerCoarseFine
        G k j initial upper tolerance budget
          (fun _ => β)
          (rankPrefixWeightedEnergyLength k j share β)
          share) := by
  apply WeightedFixedUpperLayerCoarseFine.nonempty
    initial upper tolerance budget (fun _ => β)
    htolerance hbudget
    (rankPrefixWeightedEnergyLength_pos k j share β)
  · intro i hi
    exact hβ
  · exact
      orderedFace_card_le_sum_rankPrefixWeightedEnergyLength
        hshare hβ

/-! ## The ordinary-certificate compatibility condition -/

/-- The single selected scalar inequality needed to repackage a weighted
fixed-upper choice as the corresponding rank of an ordinary coarse-target
certificate.

Weighted pigeonhole gives `gap / weight[index] ≤ ξ`.  The ordinary
certificate additionally asks for `gap ≤ card / length`; the displayed
condition is precisely the bridge between those two estimates.  It is
imposed only at the selected index. -/
def WeightedFixedUpperLayerCoarseFine.IsReciprocalCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {initial : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {tolerance : ℕ → ℝ} {budget : ℕ → ℕ}
    {weight : ℕ → ℝ} {length : ℕ} {ξ : ℝ}
    (W : WeightedFixedUpperLayerCoarseFine
      G k j initial upper tolerance budget
        weight length ξ) : Prop :=
  ξ * weight W.index ≤
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
      (length : ℝ)

/-- Reciprocal compatibility turns the weighted selected quotient into the
gap field required by an ordinary coarse-target certificate. -/
theorem WeightedFixedUpperLayerCoarseFine.gap_le_card_div
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {initial : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {tolerance : ℕ → ℝ} {budget : ℕ → ℕ}
    {weight : ℕ → ℝ} {length : ℕ} {ξ : ℝ}
    (W : WeightedFixedUpperLayerCoarseFine
      G k j initial upper tolerance budget
        weight length ξ)
    (hweight : 0 < weight W.index)
    (hcompatible : W.IsReciprocalCompatible) :
    orderedLayerAtomEnergy W.fine upper -
        orderedLayerAtomEnergy W.coarse upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        (length : ℝ) := by
  have hselected :
      orderedLayerAtomEnergy W.fine upper -
          orderedLayerAtomEnergy W.coarse upper ≤
        ξ * weight W.index :=
    (div_le_iff₀ hweight).1 W.gap_div_weight_le
  exact hselected.trans hcompatible

/-! ## From a cumulative constant-weight block to a selected gap -/

/-- If a positive constant weight pays the complete energy budget over a
block, then the reciprocal-horizon estimate of an ordinary coarse-target
certificate already gives the desired selected quotient bound.

This lemma records exactly where constant block stability is used.  For a
genuinely path-dependent weight, the cumulative weighted pigeonhole theorem
above still selects the right literal gap, but its index need not satisfy the
reciprocal-horizon field of the existing coarse-target certificate type. -/
theorem real_gap_div_le_of_card_div_and_sum_const
    {card length : ℕ} {gap share β : ℝ}
    (hlength : 0 < length) (hβ : 0 < β)
    (hgap :
      gap ≤ (card : ℝ) / (length : ℝ))
    (henergy :
      (card : ℝ) ≤
        ∑ _i ∈ Finset.range length,
          share * β) :
    gap / β ≤ share := by
  have hlengthReal : (0 : ℝ) < (length : ℝ) := by
    exact_mod_cast hlength
  have henergy' :
      (card : ℝ) ≤
        (length : ℝ) * (share * β) := by
    simpa only [Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] using henergy
  have hcardDiv :
      (card : ℝ) / (length : ℝ) ≤
        share * β := by
    apply (div_le_iff₀ hlengthReal).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      henergy'
  calc
    gap / β ≤
        ((card : ℝ) / (length : ℝ)) / β :=
      div_le_div_of_nonneg_right hgap hβ.le
    _ ≤ (share * β) / β :=
      div_le_div_of_nonneg_right hcardDiv hβ.le
    _ = share := by
      field_simp [ne_of_gt hβ]

/-! ## A selected-only constant-block margin interface -/

/-- Rank-prefix removal data in which each literal selected gap is paid by
a constant-weight energy block.

The structure is attached only to the certificate actually returned by the
selector.  It contains no assertion at another stage or another landing.
The `cumulative_energy` field is the one scalar condition needed to turn the
certificate's reciprocal-horizon field into `gap / β ≤ gapAllowance`. -/
structure RankPrefixSelectedCumulativeRemovalCompatibility
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
  gapAllowance : Fin r → ℝ
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
  cumulative_energy :
    ∀ j : Fin r,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) ≤
        ∑ _i ∈ Finset.range (length j),
          gapAllowance j *
            defectThreshold (j.1 + 1)
  deletion_budget :
    (∑ q : OrderedPositiveSubface r,
      ((upperBound q.1 : ℝ) *
          densityFloor (q.1.1 + 1) +
        gapAllowance q.1)) ≤
      ξ
  count_threshold_le :
    c ≤
      configurationHalfDensityBarrier
        (k := k) (r := r) densityFloor Finset.univ

/-- Constant-block data on the selected certificate imply the exact
literal-gap compatibility consumed by rank-prefix removal. -/
def RankPrefixSelectedCumulativeRemovalCompatibility.toCompatibility
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    {R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length}
    {ξ c : ℝ}
    (C : RankPrefixSelectedCumulativeRemovalCompatibility
      R ξ c) :
    RankPrefixSelectedRemovalCompatibility R ξ c where
  densityFloor := C.densityFloor
  defectThreshold := C.defectThreshold
  upperBound := C.upperBound
  densityFloor_pos := C.densityFloor_pos
  densityFloor_le_one := C.densityFloor_le_one
  defectThreshold_pos := C.defectThreshold_pos
  defectThreshold_rankPrefix :=
    C.defectThreshold_rankPrefix
  tolerance_rankPrefix := C.tolerance_rankPrefix
  coarse_upper_complexity := C.coarse_upper_complexity
  deletion_margin := by
    apply C.deletion_budget.trans'
    apply Finset.sum_le_sum
    intro q _hq
    exact add_le_add le_rfl
      (real_gap_div_le_of_card_div_and_sum_const
        (by
          have := R.index_lt q.1
          omega)
        (C.defectThreshold_pos (q.1.1 + 1))
        (R.coarseUpperLayerAtomEnergyGap_le_div q.1)
        (C.cumulative_energy q.1))
  count_threshold_le := C.count_threshold_le

/-- Selected-only cumulative block margins extending a structural selector.
This is a strictly factored sufficient condition for the existing removal
margin extension. -/
structure
    RankPrefixRegularitySelector.CumulativeRemovalMarginExtension
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
        (RankPrefixSelectedCumulativeRemovalCompatibility
          (S.select G initial) ξ c)

/-- Forget the cumulative block witness after it has paid every selected
literal gap. -/
theorem RankPrefixRegularitySelector.CumulativeRemovalMarginExtension.toRemovalMarginExtension
    {k r initialBound : ℕ} {ξ c : ℝ}
    {S : RankPrefixRegularitySelector k r}
    (E : S.CumulativeRemovalMarginExtension
      initialBound ξ c) :
    S.RemovalMarginExtension initialBound ξ c where
  countThreshold_pos := E.countThreshold_pos
  compatible := by
    intro G _instFintype _instDecidableEq _instNonempty
      initial hinitial
    obtain ⟨C⟩ := E.compatible G initial hinitial
    exact ⟨C.toCompatibility⟩

/-- The exact all-rank constant-block existence obligation.  Its hypotheses
mention only the chosen certificate; in particular they do not quantify over
every stage or every adaptive landing. -/
def HasRankPrefixCumulativeRemovalMarginExtensions
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    ∃ (S : RankPrefixRegularitySelector k r) (c : ℝ),
      Nonempty
        (S.CumulativeRemovalMarginExtension
          initialBound ξ c)

/-- Constant-block selected extensions imply the margin-extension endpoint
used by the uniform removal theorem. -/
theorem hasRankPrefixRemovalMarginExtensions_of_cumulative
    {k r initialBound : ℕ}
    (h :
      HasRankPrefixCumulativeRemovalMarginExtensions
        k r initialBound) :
    HasRankPrefixRemovalMarginExtensions
      k r initialBound := by
  intro ξ hξ
  obtain ⟨S, c, ⟨E⟩⟩ := h ξ hξ
  exact ⟨S, c, ⟨E.toRemovalMarginExtension⟩⟩

/-! ## Finite worst-case adjacent-rank bounds -/

/-- A finite, ambient-independent envelope for the coarse upper layer used
at rank `j`.

At the top rank the upper layer is unchanged.  Otherwise it is the coarse
output selected one rank above, so only the `(j + 1)`-st budget and horizon
enter.  This is substantially sharper than a common bound involving every
rank. -/
def rankPrefixWorstCaseUpperComplexityBound
    (r initialBound : ℕ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  if h : j.1 + 1 < r then
    initialBound *
      fixedUpperLayerComplexityFactor
        (j.1 + 1) (budget ⟨j.1 + 1, h⟩)
          (length ⟨j.1 + 1, h⟩)
  else
    initialBound

/-- Monotonicity of the tower factor upgrades the exact selected
adjacent-rank bound to the finite worst-case envelope.  No stage vector
other than the certificate's selected vector is assigned removal data. -/
theorem CoarseTargetOrderedComplexRegularityCertificate.coarse_upper_complexity_le_rankPrefixWorstCaseBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length)
    (hinitial :
      ∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.coarse.partition j.succ e) ≤
      rankPrefixWorstCaseUpperComplexityBound
        r initialBound budget length j := by
  apply
    (R.coarse_upper_complexity_le_selectedUpperBound
      hinitial j e).trans
  by_cases hj : j.1 + 1 < r
  · rw [
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
      rankPrefixWorstCaseUpperComplexityBound,
      dif_pos hj, dif_pos hj]
    apply Nat.mul_le_mul_left
    apply fixedUpperLayerComplexityFactor_monotone
    exact Nat.le_of_lt
      (R.index_lt ⟨j.1 + 1, hj⟩)
  · rw [
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
      rankPrefixWorstCaseUpperComplexityBound,
      dif_neg hj, dif_neg hj]

/-! ## The reduced all-rank numerical obligation -/

/-- The remaining selected numerical data after eliminating coarse-upper
complexity as an independent hypothesis.

The deletion budget uses the finite adjacent-rank worst-case envelope.  The
only energy hypothesis is the cumulative constant-weight payment at the
selected certificate's displayed horizon. -/
structure RankPrefixSelectedWorstCaseCumulativeParameters
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length)
    (initialBound : ℕ) (ξ c : ℝ) where
  densityFloor : ℕ → ℝ
  defectThreshold : ℕ → ℝ
  gapAllowance : Fin r → ℝ
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
  cumulative_energy :
    ∀ j : Fin r,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) ≤
        ∑ _i ∈ Finset.range (length j),
          gapAllowance j *
            defectThreshold (j.1 + 1)
  deletion_budget :
    (∑ q : OrderedPositiveSubface r,
      ((rankPrefixWorstCaseUpperComplexityBound
            r initialBound budget length q.1 : ℝ) *
          densityFloor (q.1.1 + 1) +
        gapAllowance q.1)) ≤
      ξ
  count_threshold_le :
    c ≤
      configurationHalfDensityBarrier
        (k := k) (r := r) densityFloor Finset.univ

/-- The adjacent-rank monotonicity theorem supplies the omitted
coarse-complexity field, turning the reduced parameters into cumulative
selected compatibility. -/
def RankPrefixSelectedWorstCaseCumulativeParameters.toCumulativeCompatibility
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    {R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length}
    {ξ c : ℝ}
    (P : RankPrefixSelectedWorstCaseCumulativeParameters
      R initialBound ξ c)
    (hinitial :
      ∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound) :
    RankPrefixSelectedCumulativeRemovalCompatibility
      R ξ c where
  densityFloor := P.densityFloor
  defectThreshold := P.defectThreshold
  upperBound :=
    rankPrefixWorstCaseUpperComplexityBound
      r initialBound budget length
  gapAllowance := P.gapAllowance
  densityFloor_pos := P.densityFloor_pos
  densityFloor_le_one := P.densityFloor_le_one
  defectThreshold_pos := P.defectThreshold_pos
  defectThreshold_rankPrefix :=
    P.defectThreshold_rankPrefix
  tolerance_rankPrefix := P.tolerance_rankPrefix
  coarse_upper_complexity := by
    intro j e
    exact
      R.coarse_upper_complexity_le_rankPrefixWorstCaseBound
        hinitial j e
  cumulative_energy := P.cumulative_energy
  deletion_budget := P.deletion_budget
  count_threshold_le := P.count_threshold_le

/-- Reduced worst-case parameters directly imply the exact selected
rank-prefix compatibility used by removal. -/
def RankPrefixSelectedWorstCaseCumulativeParameters.toCompatibility
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {tolerance : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    {R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length}
    {ξ c : ℝ}
    (P : RankPrefixSelectedWorstCaseCumulativeParameters
      R initialBound ξ c)
    (hinitial :
      ∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound) :
    RankPrefixSelectedRemovalCompatibility R ξ c :=
  (P.toCumulativeCompatibility hinitial).toCompatibility

/-- A structural selector together with the reduced selected numerical
parameters.  This is the smallest finite worst-case schedule extension
exposed by this file. -/
structure RankPrefixRegularitySelector.WorstCaseCumulativeRemovalMarginExtension
    {k r : ℕ}
    (S : RankPrefixRegularitySelector k r)
    (initialBound : ℕ) (ξ c : ℝ) : Prop where
  countThreshold_pos : 0 < c
  parameters :
    ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G]
      (initial : OrderedPartitionComplex G k r),
      (∀ (j : Fin (r + 1))
          (e : OrderedFace k j.1),
        FacePartition.complexity
            (initial.partition j e) ≤
          initialBound) →
      Nonempty
        (RankPrefixSelectedWorstCaseCumulativeParameters
          (S.select G initial) initialBound ξ c)

/-- The reduced selected numerical extension supplies the original margin
extension without any extra all-stage hypothesis. -/
theorem RankPrefixRegularitySelector.WorstCaseCumulativeRemovalMarginExtension.toRemovalMarginExtension
    {k r initialBound : ℕ} {ξ c : ℝ}
    {S : RankPrefixRegularitySelector k r}
    (E : S.WorstCaseCumulativeRemovalMarginExtension
      initialBound ξ c) :
    S.RemovalMarginExtension initialBound ξ c where
  countThreshold_pos := E.countThreshold_pos
  compatible := by
    intro G _instFintype _instDecidableEq _instNonempty
      initial hinitial
    obtain ⟨P⟩ := E.parameters G initial hinitial
    exact ⟨P.toCompatibility hinitial⟩

/-- Lean-ready statement of the remaining finite worst-case schedule
theorem.  Proving this predicate for all ranks would close the existing
rank-prefix margin-extension endpoint. -/
def HasRankPrefixWorstCaseCumulativeRemovalMarginExtensions
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    ∃ (S : RankPrefixRegularitySelector k r) (c : ℝ),
      Nonempty
        (S.WorstCaseCumulativeRemovalMarginExtension
          initialBound ξ c)

/-- The reduced worst-case schedule theorem is sufficient for the original
all-rank margin-extension obligation. -/
theorem hasRankPrefixRemovalMarginExtensions_of_worstCaseCumulative
    {k r initialBound : ℕ}
    (h :
      HasRankPrefixWorstCaseCumulativeRemovalMarginExtensions
        k r initialBound) :
    HasRankPrefixRemovalMarginExtensions
      k r initialBound := by
  intro ξ hξ
  obtain ⟨S, c, ⟨E⟩⟩ := h ξ hξ
  exact
    ⟨S, c, ⟨E.toRemovalMarginExtension⟩⟩

/-! ## Positivity of the rank-prefix product -/

/-- Strict positivity of every finite half-density product under strictly
positive density floors. -/
theorem configurationHalfDensityBarrier_pos_of_pos
    {k r : ℕ} (densityFloor : ℕ → ℝ)
    (hdensity : ∀ m, 0 < densityFloor m)
    (s : Finset (PositiveOrderedFace k r)) :
    0 <
      configurationHalfDensityBarrier densityFloor s := by
  unfold configurationHalfDensityBarrier
  exact Finset.prod_pos fun e _he =>
    div_pos (hdensity e.rank) (by norm_num)

/-- In particular, every triangular rank-prefix barrier is positive. -/
theorem configurationRankPrefixBarrier_pos_of_pos
    (k r : ℕ) (densityFloor : ℕ → ℝ)
    (hdensity : ∀ m, 0 < densityFloor m)
    (j : ℕ) :
    0 <
      configurationRankPrefixBarrier
        k r densityFloor j := by
  unfold configurationRankPrefixBarrier
  exact configurationHalfDensityBarrier_pos_of_pos
    densityFloor hdensity _

/-! ## Canonical triangular thresholds -/

/-- Half of the rank-prefix defect allowance.  The spare factor two makes
the required inequality immediate while retaining strict positivity. -/
noncomputable def rankPrefixHalfDefectThreshold
    (k r : ℕ) (densityFloor : ℕ → ℝ)
    (j : ℕ) : ℝ :=
  ((densityFloor j / 4) ^ 2 *
      configurationRankPrefixBarrier
        k r densityFloor j) / 2

theorem rankPrefixHalfDefectThreshold_pos
    {k r : ℕ} {densityFloor : ℕ → ℝ}
    (hdensity : ∀ m, 0 < densityFloor m)
    (j : ℕ) :
    0 <
      rankPrefixHalfDefectThreshold
        k r densityFloor j := by
  unfold rankPrefixHalfDefectThreshold
  exact div_pos
    (mul_pos
      (sq_pos_of_pos
        (div_pos (hdensity j) (by norm_num)))
      (configurationRankPrefixBarrier_pos_of_pos
        k r densityFloor hdensity j))
    (by norm_num)

theorem rankPrefixHalfDefectThreshold_le
    {k r : ℕ} {densityFloor : ℕ → ℝ}
    (hdensity : ∀ m, 0 < densityFloor m)
    (j : ℕ) :
    rankPrefixHalfDefectThreshold
        k r densityFloor j ≤
      (densityFloor j / 4) ^ 2 *
        configurationRankPrefixBarrier
          k r densityFloor j := by
  have hnonneg :
      0 ≤
        (densityFloor j / 4) ^ 2 *
          configurationRankPrefixBarrier
            k r densityFloor j := by
    exact mul_nonneg (sq_nonneg _)
      (configurationRankPrefixBarrier_nonneg
        k r densityFloor
          (fun m => (hdensity m).le) j)
  unfold rankPrefixHalfDefectThreshold
  linarith

/-! ## The unconditional rank-zero extension -/

/-- At rank zero there are no positive faces, tolerances, upper
complexities, or deletion terms.  A constant positive density floor and a
small positive defect threshold therefore give the selected compatibility
payload for every structural selector. -/
theorem hasRankPrefixRemovalMarginExtensions_zero
    (k initialBound : ℕ) :
    HasRankPrefixRemovalMarginExtensions
      k 0 initialBound := by
  intro ξ hξ
  let S : RankPrefixRegularitySelector k 0 :=
    unitRankPrefixRegularitySelector k 0
  let c : ℝ := 1 / 2
  refine ⟨S, c, ⟨{
    countThreshold_pos := by
      dsimp [c]
      norm_num
    compatible := ?_ }⟩⟩
  intro G _instFintype _instDecidableEq _instNonempty
    initial hinitial
  refine ⟨{
    densityFloor := fun _ => 1
    defectThreshold := fun _ => 1 / 32
    upperBound := fun j => Fin.elim0 j
    densityFloor_pos := by
      intro m
      norm_num
    densityFloor_le_one := by
      intro m
      norm_num
    defectThreshold_pos := by
      intro m
      norm_num
    defectThreshold_rankPrefix := by
      intro j
      have hempty :
          positiveOrderedFacesUpToRank k 0 j = ∅ := by
        ext e
        exact Fin.elim0 e.lowerRank
      rw [configurationRankPrefixBarrier, hempty]
      norm_num [configurationHalfDensityBarrier]
    tolerance_rankPrefix := fun e =>
      Fin.elim0 e.lowerRank
    coarse_upper_complexity := fun j =>
      Fin.elim0 j
    deletion_margin := by
      simpa using hξ.le
    count_threshold_le := by
      dsimp [c]
      have hempty :
          (Finset.univ :
            Finset (PositiveOrderedFace k 0)) = ∅ := by
        ext e
        exact Fin.elim0 e.lowerRank
      rw [hempty]
      norm_num [configurationHalfDensityBarrier] }⟩

/-! ## The unconditional rank-one extension -/

/-- At rank one the coarse upper layer is the unchanged input top layer.
Consequently its complexity is bounded before regularity is run, and the
rank-prefix parameters close without any feedback through a higher rank.

This gives a genuine inhabitant of the new margin-extension interface, not
merely the already known semantic rank-one removal theorem. -/
theorem hasRankPrefixRemovalMarginExtensions_one
    (k initialBound : ℕ) :
    HasRankPrefixRemovalMarginExtensions
      k 1 initialBound := by
  intro ξ hξ
  let ρ : ℝ :=
    orderedRemovalDensityFloor 1 initialBound ξ
  let densityFloor : ℕ → ℝ := fun _ => ρ
  let defectThreshold : ℕ → ℝ :=
    rankPrefixHalfDefectThreshold
      k 1 densityFloor
  let β₁ : ℝ := defectThreshold 1
  let prefix₁ : ℝ :=
    configurationRankPrefixBarrier
      k 1 densityFloor 1
  let τ : ℝ := ((ρ / 4) * prefix₁) / 2
  let share : ℝ :=
    ξ /
      (4 *
        ((Fintype.card
          (OrderedPositiveSubface 1) : ℝ) + 1))
  let γ : ℝ := share * β₁
  let tolerance : (j : Fin 1) → ℕ → ℝ :=
    fun _j _n => τ
  let budget : (j : Fin 1) → ℕ → ℕ :=
    orderedRemovalRegularityBudgetSchedule
      k 1 tolerance
  let length : Fin 1 → ℕ :=
    fun _j =>
      growthRegularityLength k 0 γ
  have hρ : 0 < ρ :=
    orderedRemovalDensityFloor_pos hξ
  have hρle : ρ ≤ 1 :=
    (orderedRemovalDensityFloor_le_half
      1 initialBound ξ).trans (by norm_num)
  have hdensity : ∀ m, 0 < densityFloor m :=
    fun _m => hρ
  have hβ : ∀ m, 0 < defectThreshold m := by
    intro m
    exact rankPrefixHalfDefectThreshold_pos
      hdensity m
  have hβ₁ : 0 < β₁ :=
    hβ 1
  have hprefix₁ : 0 < prefix₁ :=
    configurationRankPrefixBarrier_pos_of_pos
      k 1 densityFloor hdensity 1
  have hτ : 0 < τ := by
    dsimp only [τ]
    exact div_pos
      (mul_pos
        (div_pos hρ (by norm_num))
        hprefix₁)
      (by norm_num)
  have hshare : 0 < share := by
    dsimp only [share]
    positivity
  have hγ : 0 < γ :=
    mul_pos hshare hβ₁
  let S : RankPrefixRegularitySelector k 1 :=
    rankPrefixRegularitySelectorOfSchedules
      k 1 tolerance budget length
      (fun _j _n => hτ)
      (by
        intro j n
        exact
          orderedRemovalRegularityBudgetSchedule_spec
            (fun _j _n => hτ) j n)
      (by
        intro j
        exact growthRegularityLength_pos k 0 γ)
  let barrier : ℝ :=
    configurationHalfDensityBarrier
      (k := k) (r := 1)
      densityFloor Finset.univ
  let c : ℝ := barrier / 2
  have hbarrier : 0 < barrier :=
    configurationHalfDensityBarrier_pos_of_pos
      densityFloor hdensity Finset.univ
  refine ⟨S, c, ⟨{
    countThreshold_pos := div_pos hbarrier (by norm_num)
    compatible := ?_ }⟩⟩
  intro G _instFintype _instDecidableEq _instNonempty
    initial hinitial
  let R :=
    S.select G initial
  have hcoarse :
      ∀ (j : Fin 1)
          (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
            (R.coarse.partition j.succ e) ≤
          initialBound := by
    intro j e
    have hselected :=
      R.coarse_upper_complexity_le_selectedUpperBound
        hinitial j e
    have hnot : ¬ j.1 + 1 < 1 := by omega
    simpa [
      CoarseTargetOrderedComplexRegularityCertificate.coarseTargetSelectedUpperComplexityBound,
      hnot] using hselected
  have hgap :
      ∀ j : Fin 1,
        R.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
          γ := by
    intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    calc
      R.toCoarseFine.coarseUpperLayerAtomEnergyGap 0 ≤
          (Fintype.card (OrderedFace k 1) : ℝ) /
            (S.length 0 : ℝ) := by
        simpa [
          OrderedCoarseFineComplex.coarseUpperLayerAtomEnergyGap,
          CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine]
          using R.gap_le (0 : Fin 1)
      _ =
          (Fintype.card (OrderedFace k 1) : ℝ) /
            (growthRegularityLength k 0 γ : ℝ) := by
        rfl
      _ ≤ γ :=
        (orderedFace_card_div_growthRegularityLength_lt
          hγ).le
  have hlow :
      (initialBound : ℝ) * ρ ≤ ξ / 4 := by
    have h :=
      orderedRemoval_complexity_mul_densityFloor_le_quarter
        (r := 1) (M := initialBound) hξ
    simpa [orderedRemovalComplexityCoefficient,
      orderedRemovalTopSubfaceCount,
      card_orderedPositiveSubface_one, ρ] using h
  have hgapDiv :
      γ / β₁ = share := by
    dsimp only [γ]
    field_simp [ne_of_gt hβ₁]
  have hshareLe :
      (Fintype.card
          (OrderedPositiveSubface 1) : ℝ) *
          share ≤
        ξ / 4 := by
    rw [card_orderedPositiveSubface_one]
    dsimp only [share]
    norm_num
    have : (0 : ℝ) < 2 := by norm_num
    field_simp
    linarith
  have hdeletion :
      (∑ q : OrderedPositiveSubface 1,
        ((initialBound : ℝ) *
            densityFloor (q.1.1 + 1) +
          R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
            defectThreshold (q.1.1 + 1))) ≤
        ξ := by
    calc
      (∑ q : OrderedPositiveSubface 1,
        ((initialBound : ℝ) *
            densityFloor (q.1.1 + 1) +
          R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
            defectThreshold (q.1.1 + 1))) ≤
          ∑ _q : OrderedPositiveSubface 1,
            ((initialBound : ℝ) * ρ + share) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqrank : q.1.1 + 1 = 1 := by
          have := q.1.isLt
          omega
        apply add_le_add
        · simp [densityFloor]
        · have hgapq := hgap q.1
          have hβq :
              defectThreshold (q.1.1 + 1) = β₁ := by
            rw [hqrank]
          rw [hβq]
          calc
            R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
                  β₁ ≤
                γ / β₁ :=
              div_le_div_of_nonneg_right hgapq hβ₁.le
            _ = share := hgapDiv
      _ =
          (Fintype.card
              (OrderedPositiveSubface 1) : ℝ) *
            ((initialBound : ℝ) * ρ + share) := by
        simp only [Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      _ =
          (initialBound : ℝ) * ρ +
            (Fintype.card
              (OrderedPositiveSubface 1) : ℝ) * share := by
        rw [card_orderedPositiveSubface_one]
        ring
      _ ≤ ξ / 4 + ξ / 4 :=
        add_le_add hlow hshareLe
      _ ≤ ξ := by linarith
  refine ⟨{
    densityFloor := densityFloor
    defectThreshold := defectThreshold
    upperBound := fun _j => initialBound
    densityFloor_pos := hdensity
    densityFloor_le_one := fun _m => hρle
    defectThreshold_pos := hβ
    defectThreshold_rankPrefix := by
      intro j
      exact rankPrefixHalfDefectThreshold_le
        hdensity j
    tolerance_rankPrefix := ?_
    coarse_upper_complexity := hcoarse
    deletion_margin := hdeletion
    count_threshold_le := ?_ }⟩
  · intro e
    have herank : e.rank = 1 := by
      simp [PositiveOrderedFace.rank]
    simp only [selectedOrderedComplexTolerance]
    rw [herank]
    change
      τ ≤
        (ρ / 4) * prefix₁
    dsimp only [τ]
    have htarget :
        0 ≤ (ρ / 4) * prefix₁ :=
      (mul_pos
        (div_pos hρ (by norm_num))
        hprefix₁).le
    linarith
  · dsimp only [c, barrier]
    linarith

end Submission.GreenTao
