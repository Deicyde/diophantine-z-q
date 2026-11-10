import Submission.Hypergraph.RankwiseStageShiftedRegularity

/-!
# Exact-gap parameters for a selected coarse-target certificate

The stage-box removal interfaces replace every selected coarse-target
energy gap by the a priori estimate

```
card (OrderedFace k (j + 1)) / length j.
```

That replacement is harmless for a fixed certificate, but it is too coarse
for higher-rank parameter selection.  At rank two, a landing through the
last top-rank index makes the lower-rank upper complexity at least the top
horizon.  Combining that fact with the reciprocal-horizon gap estimate
creates the false numerical cycle isolated in
`not_hasAdaptiveRankwiseCoarseTargetRemovalSchedules_two`.

This file keeps the *actual selected gap*

```
R.toCoarseFine.coarseUpperLayerAtomEnergyGap j
```

all the way through cleaning.  It then gives an explicit ambient-independent
parameter package.  For `N` positive faces, `S` positive subfaces, a uniform
selected coarse-upper complexity bound `U`, and deletion allowance `ξ`, put

```
ρ = ξ / (4 (S + 1) (U + 1)),
δ = ρ^N / (8 (N + 1)),
β = δ^2,
c = ρ^N / 2,
τ₀ = δ,
γ₀ = ξ β / (4 (S + 1)).
```

If the selected tolerances are at most `τ₀` and the selected actual
coarse-upper gaps are at most `γ₀`, these values satisfy both the complete
counting margin and the complete deletion margin.  In particular `c > 0`
depends only on the displayed numerical data, not on the ambient finite
type or the selected stage.

The remaining regularity-selection problem is therefore concrete: build a
canonical selected certificate with a uniform upper bound `U` whose literal
tolerances and literal gaps meet these two explicit targets.  No margin is
required at an unselected landing, and no reciprocal horizon occurs in the
endpoint below.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## The exact-gap cleaning bridge -/

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Rankwise coarse-target cleaning with the actual selected layer gap.

Unlike `faceDeletionDensity_orderedCoarseBadBase_rankwise_le`, the defect
term is not enlarged to the reciprocal-horizon estimate stored in
`R.gap_le`.  This is the sharp form needed by a stopping-time selector. -/
theorem faceDeletionDensity_orderedCoarseBadBase_exactGap_rankwise_le
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
          R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
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
      R.toCoarseFine.coarseUpperFaceAtomEnergyGap_le_layer
        q.1 (q.2.trans e)

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Explicit common parameters -/

/-- Large-atom density floor for exact-gap selected removal. -/
noncomputable def exactGapRemovalDensityFloor
    (subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  ξ /
    (4 * ((subfaceCount : ℝ) + 1) *
      ((upperBound : ℝ) + 1))

/-- Product scale contributed by all positive faces. -/
noncomputable def exactGapRemovalCountingMass
    (faceCount subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  exactGapRemovalDensityFloor subfaceCount upperBound ξ ^ faceCount

/-- Localized square-defect error. -/
noncomputable def exactGapRemovalDefectError
    (faceCount subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  exactGapRemovalCountingMass
      faceCount subfaceCount upperBound ξ /
    (8 * ((faceCount : ℝ) + 1))

/-- Localized defect threshold. -/
noncomputable def exactGapRemovalDefectThreshold
    (faceCount subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  exactGapRemovalDefectError
      faceCount subfaceCount upperBound ξ ^ 2

/-- Ambient-independent positive pattern-count threshold. -/
noncomputable def exactGapRemovalCountThreshold
    (faceCount subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  exactGapRemovalCountingMass
      faceCount subfaceCount upperBound ξ / 2

/-- Required upper bound for the literal selected regularity tolerance. -/
noncomputable def exactGapRemovalToleranceTarget
    (faceCount subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  exactGapRemovalDefectError
    faceCount subfaceCount upperBound ξ

/-- Required upper bound for each literal selected coarse-upper layer gap. -/
noncomputable def exactGapRemovalEnergyTarget
    (faceCount subfaceCount upperBound : ℕ) (ξ : ℝ) : ℝ :=
  ξ *
      exactGapRemovalDefectThreshold
        faceCount subfaceCount upperBound ξ /
    (4 * ((subfaceCount : ℝ) + 1))

theorem exactGapRemovalDensityFloor_pos
    {subfaceCount upperBound : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    0 <
      exactGapRemovalDensityFloor
        subfaceCount upperBound ξ := by
  unfold exactGapRemovalDensityFloor
  positivity

theorem exactGapRemovalCountingMass_pos
    {faceCount subfaceCount upperBound : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    0 <
      exactGapRemovalCountingMass
        faceCount subfaceCount upperBound ξ := by
  unfold exactGapRemovalCountingMass
  exact pow_pos
    (exactGapRemovalDensityFloor_pos hξ) faceCount

theorem exactGapRemovalDefectError_pos
    {faceCount subfaceCount upperBound : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    0 <
      exactGapRemovalDefectError
        faceCount subfaceCount upperBound ξ := by
  unfold exactGapRemovalDefectError
  exact div_pos
    (exactGapRemovalCountingMass_pos hξ)
    (by positivity)

theorem exactGapRemovalDefectThreshold_pos
    {faceCount subfaceCount upperBound : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    0 <
      exactGapRemovalDefectThreshold
        faceCount subfaceCount upperBound ξ := by
  unfold exactGapRemovalDefectThreshold
  exact sq_pos_of_pos
    (exactGapRemovalDefectError_pos hξ)

theorem exactGapRemovalCountThreshold_pos
    {faceCount subfaceCount upperBound : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    0 <
      exactGapRemovalCountThreshold
        faceCount subfaceCount upperBound ξ := by
  unfold exactGapRemovalCountThreshold
  exact div_pos
    (exactGapRemovalCountingMass_pos hξ)
    (by norm_num)

theorem exactGapRemovalEnergyTarget_pos
    {faceCount subfaceCount upperBound : ℕ} {ξ : ℝ}
    (hξ : 0 < ξ) :
    0 <
      exactGapRemovalEnergyTarget
        faceCount subfaceCount upperBound ξ := by
  unfold exactGapRemovalEnergyTarget
  exact div_pos
    (mul_pos hξ
      (exactGapRemovalDefectThreshold_pos hξ))
    (by positivity)

/-! ## Finite counting and cleaning arithmetic -/

/-- The explicit defect error and tolerance target spend at most one
quarter of the density product. -/
theorem finite_exactGapRemovalCountingError_le_quarter
    {α : Type*} [Fintype α]
    (subfaceCount upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (τ : α → ℝ)
    (hτ : ∀ a, τ a ≤
      exactGapRemovalToleranceTarget
        (Fintype.card α) subfaceCount upperBound ξ) :
    (∑ a : α,
        (exactGapRemovalDefectError
            (Fintype.card α) subfaceCount upperBound ξ +
          τ a)) ≤
      exactGapRemovalCountingMass
          (Fintype.card α) subfaceCount upperBound ξ / 4 := by
  let n : ℝ := Fintype.card α
  let mass : ℝ :=
    exactGapRemovalCountingMass
      (Fintype.card α) subfaceCount upperBound ξ
  let δ : ℝ :=
    exactGapRemovalDefectError
      (Fintype.card α) subfaceCount upperBound ξ
  have hmass : 0 ≤ mass :=
    (exactGapRemovalCountingMass_pos hξ).le
  have hn : 0 ≤ n := by
    dsimp only [n]
    positivity
  have hn1 : 0 < n + 1 := by linarith
  have hfracNonneg : 0 ≤ n / (n + 1) :=
    div_nonneg hn hn1.le
  have hfracLe : n / (n + 1) ≤ 1 :=
    (div_le_one hn1).2 (by linarith)
  have hδ :
      δ = mass / (8 * (n + 1)) := by
    rfl
  have hcostIdentity :
      n * (δ + δ) =
        (mass / 4) * (n / (n + 1)) := by
    rw [hδ]
    field_simp [ne_of_gt hn1]
    ring
  have hcost :
      n * (δ + δ) ≤ mass / 4 := by
    rw [hcostIdentity]
    simpa using
      mul_le_mul_of_nonneg_left hfracLe
        (div_nonneg hmass (by norm_num))
  calc
    (∑ a : α,
        (exactGapRemovalDefectError
            (Fintype.card α) subfaceCount upperBound ξ +
          τ a)) ≤
        ∑ _a : α, (δ + δ) := by
      apply Finset.sum_le_sum
      intro a _ha
      change δ + τ a ≤ δ + δ
      have ha : τ a ≤ δ := by
        simpa [exactGapRemovalToleranceTarget, δ] using hτ a
      exact add_le_add le_rfl ha
    _ = n * (δ + δ) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      dsimp only [n]
    _ ≤ mass / 4 := hcost
    _ =
        exactGapRemovalCountingMass
          (Fintype.card α) subfaceCount upperBound ξ / 4 := by
      rfl

/-- The explicit positive count threshold lies below the complete density
product minus all selected counting errors. -/
theorem finite_exactGapRemovalCountingMargin
    {α : Type*} [Fintype α]
    (subfaceCount upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (τ : α → ℝ)
    (hτ : ∀ a, τ a ≤
      exactGapRemovalToleranceTarget
        (Fintype.card α) subfaceCount upperBound ξ) :
    exactGapRemovalCountThreshold
        (Fintype.card α) subfaceCount upperBound ξ ≤
      (∏ _a : α,
        exactGapRemovalDensityFloor
          subfaceCount upperBound ξ) -
        (∑ a : α,
          (exactGapRemovalDefectError
              (Fintype.card α) subfaceCount upperBound ξ +
            τ a)) := by
  have herror :=
    finite_exactGapRemovalCountingError_le_quarter
      subfaceCount upperBound hξ τ hτ
  have hmass :
      0 ≤
        exactGapRemovalCountingMass
          (Fintype.card α) subfaceCount upperBound ξ :=
    (exactGapRemovalCountingMass_pos hξ).le
  rw [show
      (∏ _a : α,
          exactGapRemovalDensityFloor
            subfaceCount upperBound ξ) =
        exactGapRemovalCountingMass
          (Fintype.card α) subfaceCount upperBound ξ by
    simp [exactGapRemovalCountingMass]]
  unfold exactGapRemovalCountThreshold
  linarith

/-- The low-density part of exact-gap cleaning spends at most one quarter
of the deletion allowance. -/
theorem exactGapRemoval_lowDensityCost_le_quarter
    (subfaceCount upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    (subfaceCount : ℝ) * (upperBound : ℝ) *
        exactGapRemovalDensityFloor
          subfaceCount upperBound ξ ≤
      ξ / 4 := by
  let s : ℝ := subfaceCount
  let u : ℝ := upperBound
  have hs : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hu : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hs1 : 0 < s + 1 := by linarith
  have hu1 : 0 < u + 1 := by linarith
  have hprodPos : 0 < (s + 1) * (u + 1) :=
    mul_pos hs1 hu1
  have hprod :
      s * u ≤ (s + 1) * (u + 1) := by
    nlinarith
  have hratio :
      s * u / ((s + 1) * (u + 1)) ≤ 1 :=
    (div_le_one hprodPos).2 hprod
  have hidentity :
      s * u *
          exactGapRemovalDensityFloor
            subfaceCount upperBound ξ =
        (ξ / 4) *
          (s * u / ((s + 1) * (u + 1))) := by
    unfold exactGapRemovalDensityFloor
    dsimp only [s, u]
    field_simp [ne_of_gt hs1, ne_of_gt hu1]
  rw [hidentity]
  simpa using
    mul_le_mul_of_nonneg_left hratio
      (div_nonneg hξ.le (by norm_num))

/-- Dividing the explicit selected energy target by the defect threshold
cancels the latter exactly. -/
theorem exactGapRemovalEnergyTarget_div_defectThreshold
    {faceCount subfaceCount upperBound : ℕ}
    {ξ : ℝ} (hξ : 0 < ξ) :
    exactGapRemovalEnergyTarget
          faceCount subfaceCount upperBound ξ /
        exactGapRemovalDefectThreshold
          faceCount subfaceCount upperBound ξ =
      ξ / (4 * ((subfaceCount : ℝ) + 1)) := by
  unfold exactGapRemovalEnergyTarget
  have hβ :
      exactGapRemovalDefectThreshold
          faceCount subfaceCount upperBound ξ ≠ 0 :=
    ne_of_gt (exactGapRemovalDefectThreshold_pos hξ)
  field_simp [hβ]

/-- The actual-gap part of cleaning also spends at most one quarter of the
deletion allowance. -/
theorem exactGapRemoval_gapCost_le_quarter
    (faceCount subfaceCount upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ) :
    (subfaceCount : ℝ) *
        (exactGapRemovalEnergyTarget
            faceCount subfaceCount upperBound ξ /
          exactGapRemovalDefectThreshold
            faceCount subfaceCount upperBound ξ) ≤
      ξ / 4 := by
  rw [exactGapRemovalEnergyTarget_div_defectThreshold hξ]
  let s : ℝ := subfaceCount
  have hs : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hs1 : 0 < s + 1 := by linarith
  have hratio : s / (s + 1) ≤ 1 :=
    (div_le_one hs1).2 (by linarith)
  have hidentity :
      s * (ξ / (4 * (s + 1))) =
        (ξ / 4) * (s / (s + 1)) := by
    field_simp [ne_of_gt hs1]
  change s * (ξ / (4 * (s + 1))) ≤ ξ / 4
  rw [hidentity]
  simpa using
    mul_le_mul_of_nonneg_left hratio
      (div_nonneg hξ.le (by norm_num))

/-- Uniform upper-complexity and actual-gap bounds imply the complete
finite deletion margin for the explicit common parameters. -/
theorem finite_exactGapRemovalDeletionMargin
    {σ : Type*} [Fintype σ]
    (faceCount upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (upper : σ → ℕ)
    (gap : σ → ℝ)
    (hupper : ∀ q, upper q ≤ upperBound)
    (_hgap_nonneg : ∀ q, 0 ≤ gap q)
    (hgap : ∀ q, gap q ≤
      exactGapRemovalEnergyTarget
        faceCount (Fintype.card σ) upperBound ξ) :
    (∑ q : σ,
        ((upper q : ℝ) *
            exactGapRemovalDensityFloor
              (Fintype.card σ) upperBound ξ +
          gap q /
            exactGapRemovalDefectThreshold
              faceCount (Fintype.card σ) upperBound ξ)) ≤
      ξ := by
  let ρ :=
    exactGapRemovalDensityFloor
      (Fintype.card σ) upperBound ξ
  let β :=
    exactGapRemovalDefectThreshold
      faceCount (Fintype.card σ) upperBound ξ
  let γ :=
    exactGapRemovalEnergyTarget
      faceCount (Fintype.card σ) upperBound ξ
  have hρ : 0 ≤ ρ :=
    (exactGapRemovalDensityFloor_pos hξ).le
  have hβ : 0 < β :=
    exactGapRemovalDefectThreshold_pos hξ
  have hsum :
      (∑ q : σ,
          ((upper q : ℝ) * ρ + gap q / β)) ≤
        ∑ _q : σ,
          ((upperBound : ℝ) * ρ + γ / β) := by
    apply Finset.sum_le_sum
    intro q _hq
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (hupper q)) hρ
    · exact div_le_div_of_nonneg_right
        (hgap q) hβ.le
  have hlow :=
    exactGapRemoval_lowDensityCost_le_quarter
      (Fintype.card σ) upperBound hξ
  have henergy :=
    exactGapRemoval_gapCost_le_quarter
      faceCount (Fintype.card σ) upperBound hξ
  calc
    (∑ q : σ,
        ((upper q : ℝ) *
            exactGapRemovalDensityFloor
              (Fintype.card σ) upperBound ξ +
          gap q /
            exactGapRemovalDefectThreshold
              faceCount (Fintype.card σ) upperBound ξ)) =
        ∑ q : σ,
          ((upper q : ℝ) * ρ + gap q / β) := by
      rfl
    _ ≤
        ∑ _q : σ,
          ((upperBound : ℝ) * ρ + γ / β) := hsum
    _ =
        (Fintype.card σ : ℝ) *
          ((upperBound : ℝ) * ρ + γ / β) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    _ =
        (Fintype.card σ : ℝ) *
              (upperBound : ℝ) * ρ +
          (Fintype.card σ : ℝ) * (γ / β) := by
      ring
    _ ≤ ξ / 4 + ξ / 4 :=
      add_le_add hlow henergy
    _ ≤ ξ := by linarith

/-! ## Exact-gap selected compatibility -/

/-- Rankwise cleaning and counting data attached to one selected
coarse-target certificate, retaining its literal selected energy gaps. -/
structure ExactGapRankwiseSelectedCoarseTargetCompatibility
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
        R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
          defectThreshold q.1)) ≤
      ξ

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Exact-gap compatibility at the selected certificate gives the semantic
cover and deletion bound. -/
theorem removal_of_exactGapRankwiseSelectedCompatibility
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
    (C : ExactGapRankwiseSelectedCoarseTargetCompatibility
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
    R.faceDeletionDensity_orderedCoarseBadBase_exactGap_rankwise_le
      C.upperBound C.coarse_upper_complexity
      αs βs
      (fun j => hαs (j + 1))
      (fun j => hβs (j + 1)) e
  refine hdelete.trans ?_
  simpa [αs, βs] using C.deletion_margin

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Constructing compatibility from the two selected bounds -/

/-- The explicit parameter package constructs exact-gap compatibility.

The only certificate-specific obligations are a uniform coarse-upper
complexity bound, the literal selected tolerance target, and the literal
selected layer-gap target. -/
noncomputable def exactGapRankwiseSelectedCompatibilityOfBounds
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (htolerance_nonneg :
      ∀ j,
        0 ≤ selectedOrderedComplexTolerance
          ε R.index j)
    (htolerance :
      ∀ j,
        selectedOrderedComplexTolerance
            ε R.index j ≤
          exactGapRemovalToleranceTarget
            (Fintype.card (PositiveOrderedFace k r))
            (Fintype.card (OrderedPositiveSubface r))
            upperBound ξ)
    (hcoarse :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (R.coarse.partition j.succ e) ≤ upperBound)
    (hgap :
      ∀ j,
        R.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
          exactGapRemovalEnergyTarget
            (Fintype.card (PositiveOrderedFace k r))
            (Fintype.card (OrderedPositiveSubface r))
            upperBound ξ) :
    ExactGapRankwiseSelectedCoarseTargetCompatibility
      R ξ
        (exactGapRemovalCountThreshold
          (Fintype.card (PositiveOrderedFace k r))
          (Fintype.card (OrderedPositiveSubface r))
          upperBound ξ) where
  upperBound := fun _ => upperBound
  densityFloor := fun _ =>
    exactGapRemovalDensityFloor
      (Fintype.card (OrderedPositiveSubface r))
      upperBound ξ
  defectThreshold := fun _ =>
    exactGapRemovalDefectThreshold
      (Fintype.card (PositiveOrderedFace k r))
      (Fintype.card (OrderedPositiveSubface r))
      upperBound ξ
  defectError := fun _ =>
    exactGapRemovalDefectError
      (Fintype.card (PositiveOrderedFace k r))
      (Fintype.card (OrderedPositiveSubface r))
      upperBound ξ
  densityFloor_nonneg := fun _ =>
    (exactGapRemovalDensityFloor_pos hξ).le
  defectThreshold_pos := fun _ =>
    exactGapRemovalDefectThreshold_pos hξ
  defectError_nonneg := fun _ =>
    (exactGapRemovalDefectError_pos hξ).le
  tolerance_nonneg := htolerance_nonneg
  defectThreshold_le_sq := fun _ => le_rfl
  counting_margin := by
    exact
      finite_exactGapRemovalCountingMargin
        (Fintype.card (OrderedPositiveSubface r))
        upperBound hξ
        (fun e : PositiveOrderedFace k r =>
          selectedOrderedComplexTolerance
            ε R.index e.lowerRank)
        (fun e => htolerance e.lowerRank)
  coarse_upper_complexity := hcoarse
  deletion_margin := by
    exact
      finite_exactGapRemovalDeletionMargin
        (Fintype.card (PositiveOrderedFace k r))
        upperBound hξ
        (fun _q : OrderedPositiveSubface r => upperBound)
        (fun q =>
          R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1)
        (fun _q => le_rfl)
        (fun q =>
          by
            rw [
              R.toCoarseFine.coarseUpperLayerAtomEnergyGap_eq_sum_face]
            exact Finset.sum_nonneg fun e _ =>
              R.toCoarseFine.coarseUpperFaceAtomEnergyGap_nonneg q.1 e)
        (fun q => hgap q.1)

/-- Direct constructive endpoint: the explicit tolerance, actual-gap, and
upper-complexity bounds on one selected certificate yield a removal cover.
No reciprocal horizon and no all-landing numerical hypothesis occurs. -/
theorem exists_orderedPatternRemoval_of_selectedExactGapBounds
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
    (upperBound : ℕ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (htolerance_nonneg :
      ∀ j,
        0 ≤ selectedOrderedComplexTolerance
          ε R.index j)
    (htolerance :
      ∀ j,
        selectedOrderedComplexTolerance
            ε R.index j ≤
          exactGapRemovalToleranceTarget
            (Fintype.card
              (PositiveOrderedFace k (n + 1)))
            (Fintype.card
              (OrderedPositiveSubface (n + 1)))
            upperBound ξ)
    (hcoarse :
      ∀ (j : Fin (n + 1))
          (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (R.coarse.partition j.succ e) ≤ upperBound)
    (hgap :
      ∀ j,
        R.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
          exactGapRemovalEnergyTarget
            (Fintype.card
              (PositiveOrderedFace k (n + 1)))
            (Fintype.card
              (OrderedPositiveSubface (n + 1)))
            upperBound ξ)
    (hcount :
      H.toWeighted.patternCount <
        exactGapRemovalCountThreshold
          (Fintype.card
            (PositiveOrderedFace k (n + 1)))
          (Fintype.card
            (OrderedPositiveSubface (n + 1)))
          upperBound ξ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k (n + 1),
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  let C :=
    exactGapRankwiseSelectedCompatibilityOfBounds
      R upperBound hξ
      htolerance_nonneg htolerance hcoarse hgap
  exact
    R.removal_of_exactGapRankwiseSelectedCompatibility
      hrank H hinitial C hcount

end Submission.GreenTao
