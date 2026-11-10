import Submission.Hypergraph.GrowthFunctionComplexRegularity
import Submission.Hypergraph.CoarseOrderedRemovalTheorem

/-!
# Hierarchical good atoms for growth-function regularity

This file connects the literal rankwise output of
`GrowthFunctionOrderedComplexRegularityCertificate` to the good-atom,
cleaning, and counting interfaces.

At a selected rank `j`, write

```
τ_j = 1 / F(M_j),
ρ_j = 1 / log(F(M_j)),
```

where `M_j` is the actual selected coarse complexity bound.  Following
Tao's good-atom hierarchy, we use `ρ_j` as the density floor and `τ_j` as
the localized square-defect threshold.  Thus the elementary localized
Cauchy--Schwarz contribution in the current configuration-counting API is
exactly `sqrt τ_j`.

The cleaning estimates retain the selected rank:

* for fine upper atoms, the bad mass is at most
  `fineUpperComplexity_j * ρ_j + γ_j / τ_j`;
* for coarse upper atoms, the atom-energy comparison costs one additional
  fine-upper complexity factor, giving
  `coarseUpperComplexity_j * ρ_j
    + fineUpperComplexity_j * γ_j / τ_j`.

No maximum over ranks and no replacement of the selected tolerance by a
global error is made.  The final section specializes the rankwise mixed
configuration-counting theorem and the semantic coarse-removal cover
theorem to these schedules.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Positive-rank schedules -/

/-- Extend a schedule on adjacent ranks `Fin r` to the natural-number
schedule expected by the good-atom API.  Only positive ranks `1, ..., r`
are relevant; all other values are set to the harmless positive default
`1`.  Positivity outside the relevant range is useful because the existing
cleaning API asks for a globally positive natural-number schedule. -/
noncomputable def positiveRankSchedule
    {r : ℕ} (θ : Fin r → ℝ) (n : ℕ) : ℝ :=
  if h : 0 < n ∧ n ≤ r then
    θ ⟨n - 1, by omega⟩
  else
    1

@[simp]
theorem positiveRankSchedule_succ
    {r : ℕ} (θ : Fin r → ℝ) (j : Fin r) :
    positiveRankSchedule θ (j.1 + 1) = θ j := by
  rw [positiveRankSchedule, dif_pos]
  · congr 1
  · exact ⟨Nat.succ_pos _, j.isLt⟩

theorem positiveRankSchedule_nonneg
    {r : ℕ} {θ : Fin r → ℝ}
    (hθ : ∀ j, 0 ≤ θ j) :
    ∀ n, 0 ≤ positiveRankSchedule θ n := by
  intro n
  rw [positiveRankSchedule]
  split_ifs with h
  · exact hθ ⟨n - 1, by omega⟩
  · norm_num

theorem positiveRankSchedule_pos
    {r : ℕ} {θ : Fin r → ℝ}
    (hθ : ∀ j, 0 < θ j) :
    ∀ n, 0 < positiveRankSchedule θ n := by
  intro n
  rw [positiveRankSchedule]
  split_ifs with h
  · exact hθ ⟨n - 1, by omega⟩
  · norm_num

theorem positiveRankSchedule_sq
    {r : ℕ} (θ : Fin r → ℝ) (n : ℕ) :
    positiveRankSchedule (fun j => (θ j) ^ 2) n =
      (positiveRankSchedule θ n) ^ 2 := by
  rw [positiveRankSchedule, positiveRankSchedule]
  split_ifs <;> simp

/-! ## Literal selected thresholds -/

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- The selected natural growth value `F(M_j)`. -/
noncomputable def selectedRankGrowthValue
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) : ℕ :=
  F (selectedGrowthCoarseComplexityBound
    k r initialBound F R.index j)

/-- The exact reciprocal tolerance selected at rank `j`. -/
noncomputable def selectedRankTolerance
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) : ℝ :=
  1 / (R.selectedRankGrowthValue j : ℝ)

/-- Tao's rankwise large-atom density floor `1 / log(F(M_j))`. -/
noncomputable def selectedRankDensityFloor
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) : ℝ :=
  1 / Real.log (R.selectedRankGrowthValue j : ℝ)

/-- Square-root defect error contributed by the localized threshold
`τ_j`. -/
noncomputable def selectedRankDefectError
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) : ℝ :=
  Real.sqrt (R.selectedRankTolerance j)

/-- The selected reciprocal tolerance is strictly positive. -/
theorem selectedRankTolerance_pos
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    0 < R.selectedRankTolerance j := by
  unfold selectedRankTolerance
  exact one_div_pos.mpr
    (by
      exact_mod_cast
        F.positive
          (selectedGrowthCoarseComplexityBound
            k r initialBound F R.index j))

theorem selectedRankTolerance_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    0 ≤ R.selectedRankTolerance j :=
  (R.selectedRankTolerance_pos j).le

theorem selectedRankTolerance_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    R.selectedRankTolerance j ≤ 1 := by
  unfold selectedRankTolerance
  calc
    1 / (R.selectedRankGrowthValue j : ℝ) ≤ 1 / 1 := by
      apply one_div_le_one_div_of_le
      · norm_num
      · exact_mod_cast
          F.one_le
            (selectedGrowthCoarseComplexityBound
              k r initialBound F R.index j)
    _ = 1 := by norm_num

theorem selectedRankDensityFloor_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    0 ≤ R.selectedRankDensityFloor j := by
  unfold selectedRankDensityFloor
  apply one_div_nonneg.mpr
  apply Real.log_nonneg
  exact_mod_cast
    F.one_le
      (selectedGrowthCoarseComplexityBound
        k r initialBound F R.index j)

theorem selectedRankDensityFloor_pos_of_one_lt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r)
    (hgrowth : 1 < R.selectedRankGrowthValue j) :
    0 < R.selectedRankDensityFloor j := by
  unfold selectedRankDensityFloor
  apply one_div_pos.mpr
  apply Real.log_pos
  exact_mod_cast hgrowth

theorem selectedRankDefectError_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    0 ≤ R.selectedRankDefectError j :=
  Real.sqrt_nonneg _

theorem selectedRankDefectError_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    (R.selectedRankDefectError j) ^ 2 =
      R.selectedRankTolerance j := by
  exact Real.sq_sqrt (R.selectedRankTolerance_nonneg j)

/-- Density-floor schedule attached to the selected rankwise growth
values. -/
noncomputable def selectedDensityFloor
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    ℕ → ℝ :=
  positiveRankSchedule R.selectedRankDensityFloor

/-- Localized square-defect threshold attached to the selected rankwise
tolerances. -/
noncomputable def selectedDefectThreshold
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    ℕ → ℝ :=
  positiveRankSchedule R.selectedRankTolerance

/-- Natural-number schedule for the square-root localized-defect error. -/
noncomputable def selectedDefectError
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    ℕ → ℝ :=
  positiveRankSchedule R.selectedRankDefectError

@[simp]
theorem selectedDensityFloor_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    R.selectedDensityFloor (j.1 + 1) =
      R.selectedRankDensityFloor j :=
  positiveRankSchedule_succ _ j

@[simp]
theorem selectedDefectThreshold_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    R.selectedDefectThreshold (j.1 + 1) =
      R.selectedRankTolerance j :=
  positiveRankSchedule_succ _ j

@[simp]
theorem selectedDefectError_succ
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    R.selectedDefectError (j.1 + 1) =
      R.selectedRankDefectError j :=
  positiveRankSchedule_succ _ j

@[simp]
theorem selectedDensityFloor_positiveFace_rank
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (e : PositiveOrderedFace k r) :
    R.selectedDensityFloor e.rank =
      R.selectedRankDensityFloor e.lowerRank := by
  simp [PositiveOrderedFace.rank]

@[simp]
theorem selectedDefectThreshold_positiveFace_rank
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (e : PositiveOrderedFace k r) :
    R.selectedDefectThreshold e.rank =
      R.selectedRankTolerance e.lowerRank := by
  simp [PositiveOrderedFace.rank]

@[simp]
theorem selectedDefectError_positiveFace_rank
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (e : PositiveOrderedFace k r) :
    R.selectedDefectError e.rank =
      R.selectedRankDefectError e.lowerRank := by
  simp [PositiveOrderedFace.rank]

theorem selectedDensityFloor_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    ∀ n, 0 ≤ R.selectedDensityFloor n :=
  positiveRankSchedule_nonneg R.selectedRankDensityFloor_nonneg

theorem selectedDefectThreshold_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    ∀ n, 0 ≤ R.selectedDefectThreshold n := by
  exact positiveRankSchedule_nonneg
    R.selectedRankTolerance_nonneg

theorem selectedDefectThreshold_pos
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    ∀ n, 0 < R.selectedDefectThreshold n :=
  positiveRankSchedule_pos R.selectedRankTolerance_pos

theorem selectedDefectError_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (n : ℕ) :
    0 ≤ R.selectedDefectError n :=
  positiveRankSchedule_nonneg
    R.selectedRankDefectError_nonneg n

theorem selectedDefectThreshold_eq_defectError_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (n : ℕ) :
    R.selectedDefectThreshold n =
      (R.selectedDefectError n) ^ 2 := by
  rw [selectedDefectThreshold, selectedDefectError,
    ← positiveRankSchedule_sq]
  congr 1
  funext j
  exact (Real.sq_sqrt
    (R.selectedRankTolerance_nonneg j)).symm

/-- The selected certificate regarded as the coarse/fine complex consumed
by goodness, cleaning, and configuration counting. -/
def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

@[simp]
theorem toCoarseFine_coarse
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    R.toCoarseFine.coarse = R.coarse :=
  rfl

@[simp]
theorem toCoarseFine_fine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    R.toCoarseFine.fine = R.fine :=
  rfl

/-- The certificate's regularity field, named using the literal selected
rank tolerance. -/
theorem regular_selectedRankTolerance
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    IsFullyPreliminaryOrderedRegular R.fine
      R.selectedRankTolerance := by
  unfold selectedRankTolerance
  exact R.regular

/-- Selected fine-upper complexity at the adjacent rank `j + 1`. -/
noncomputable def selectedFineUpperComplexityBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) : ℕ :=
  selectedGrowthFineLayerComplexityBound
    k r initialBound F R.index j.succ

/-- Selected coarse-upper complexity at the adjacent rank `j + 1`. -/
noncomputable def selectedCoarseUpperComplexityBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) : ℕ :=
  selectedGrowthCoarseLayerComplexityBound
    k r initialBound F R.index j.succ

theorem fine_upper_complexity_le_selected
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.fine.partition j.succ e) ≤
      R.selectedFineUpperComplexityBound j := by
  exact R.fine_complexity j.succ e

theorem coarse_upper_complexity_le_selected
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.coarse.partition j.succ e) ≤
      R.selectedCoarseUpperComplexityBound j := by
  exact R.coarse_complexity j.succ e

/-! ## Fine-upper hierarchical good atoms -/

/-- Canonical local goodness at rank `j`, with density floor `ρ_j` and
localized square-defect threshold `τ_j`. -/
def SelectedFineAtomIsGoodAtBoundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1))
    (x : Fin (j.1 + 1) → G) : Prop :=
  OrderedAtomIsGoodAtBoundary
    (R.fine.partition j.castSucc)
    (R.coarse.partition j.castSucc)
    e
    (R.fine.partition j.succ e)
    (partitionAtomAt (R.fine.partition j.succ e) x)
    x
    (R.selectedRankDensityFloor j)
    (R.selectedRankTolerance j)

/-- Fine-upper tuples rejected by the canonical selected thresholds. -/
noncomputable def selectedFineBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    Finset (Fin (j.1 + 1) → G) :=
  orderedOwnAtomBadBaseSupport
    (R.fine.partition j.castSucc)
    (R.coarse.partition j.castSucc)
    e
    (R.fine.partition j.succ e)
    (R.selectedRankDensityFloor j)
    (R.selectedRankTolerance j)

/-- Avoidance of the selected fine-upper bad base gives the literal local
density and localized square-defect inequalities. -/
theorem selectedFineAtomIsGoodAtBoundary_of_not_mem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1))
    (x : Fin (j.1 + 1) → G)
    (hx : x ∉ R.selectedFineBadBaseSupport j e) :
    R.SelectedFineAtomIsGoodAtBoundary j e x := by
  apply orderedAtomIsGoodAtBoundary_of_not_mem_badBase
  intro hbad
  exact hx
    ((mem_orderedOwnAtomBadBaseSupport
      (R.fine.partition j.castSucc)
      (R.coarse.partition j.castSucc)
      e
      (R.fine.partition j.succ e)
      (R.selectedRankDensityFloor j)
      (R.selectedRankTolerance j) x).2 hbad)

/-- The selected local goodness predicate gives the exact localized
square-defect mass bound used by configuration counting. -/
theorem SelectedFineAtomIsGoodAtBoundary.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1))
    (x : Fin (j.1 + 1) → G)
    (hgood : R.SelectedFineAtomIsGoodAtBoundary j e x) :
    orderedLocalizedAtomDefectSq
        (R.fine.partition j.castSucc)
        (R.coarse.partition j.castSucc)
        e
        (R.fine.partition j.succ e)
        (partitionAtomAt (R.fine.partition j.succ e) x)
        (orderedBoundaryAtomAt
          (R.coarse.partition j.castSucc) e x) ≤
      R.selectedRankTolerance j *
        orderedBoundaryAtomMass
          (R.coarse.partition j.castSucc) e
          (orderedBoundaryAtomAt
            (R.coarse.partition j.castSucc) e x) := by
  exact OrderedAtomIsGoodAtBoundary.localized_defect
    (R.fine.partition j.castSucc)
    (R.coarse.partition j.castSucc)
    e
    (R.fine.partition j.succ e)
    (partitionAtomAt (R.fine.partition j.succ e) x)
    x
    (R.selectedRankDensityFloor j)
    (R.selectedRankTolerance j)
    hgood

/-- Exact fine-upper bad-base estimate before inserting selected numerical
bounds. -/
theorem mean_indicator_selectedFineBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    mean (finsetIndicator
        (R.selectedFineBadBaseSupport j e)) ≤
      (FacePartition.complexity
          (R.fine.partition j.succ e) : ℝ) *
          R.selectedRankDensityFloor j +
        R.toCoarseFine.faceAtomEnergyGap j e /
          R.selectedRankTolerance j := by
  change
    mean (finsetIndicator
        (orderedOwnAtomBadBaseSupport
          (R.fine.partition j.castSucc)
          (R.coarse.partition j.castSucc)
          e (R.fine.partition j.succ e)
          (R.selectedRankDensityFloor j)
          (R.selectedRankTolerance j))) ≤
      (FacePartition.complexity
          (R.fine.partition j.succ e) : ℝ) *
          R.selectedRankDensityFloor j +
        (orderedAtomEnergy
            (R.fine.partition j.castSucc) e
            (R.fine.partition j.succ e) -
          orderedAtomEnergy
            (R.coarse.partition j.castSucc) e
            (R.fine.partition j.succ e)) /
          R.selectedRankTolerance j
  exact mean_indicator_orderedOwnAtomBadBaseSupport_le
    (fun f => R.refines j.castSucc f)
    e
    (R.fine.partition j.succ e)
    (R.selectedRankDensityFloor_nonneg j)
    (R.selectedRankTolerance_pos j)

/-- The fine-upper bad mass consumes exactly the selected upper complexity,
the literal selected tolerance, and the rank-`j` energy-gap target. -/
theorem mean_indicator_selectedFineBadBaseSupport_le_selected
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    mean (finsetIndicator
        (R.selectedFineBadBaseSupport j e)) ≤
      (R.selectedFineUpperComplexityBound j : ℝ) *
          R.selectedRankDensityFloor j +
        γ j / R.selectedRankTolerance j := by
  have hface :
      R.toCoarseFine.faceAtomEnergyGap j e ≤ γ j := by
    exact
      (R.toCoarseFine.faceAtomEnergyGap_le_layer j e).trans
        (by
          simpa [toCoarseFine,
            OrderedCoarseFineComplex.layerAtomEnergyGap] using
            R.gap_le j)
  exact
    (R.mean_indicator_selectedFineBadBaseSupport_le j e).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (R.fine_upper_complexity_le_selected j e))
          (R.selectedRankDensityFloor_nonneg j))
        (div_le_div_of_nonneg_right hface
          (R.selectedRankTolerance_nonneg j)))

/-! ## Coarse-upper hierarchical good atoms -/

/-- Canonical mixed goodness when the chosen upper atom belongs to the
coarse upper partition. -/
def SelectedCoarseAtomIsGoodAtBoundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1))
    (x : Fin (j.1 + 1) → G) : Prop :=
  OrderedAtomIsGoodAtBoundary
    (R.fine.partition j.castSucc)
    (R.coarse.partition j.castSucc)
    e
    (R.coarse.partition j.succ e)
    (partitionAtomAt (R.coarse.partition j.succ e) x)
    x
    (R.selectedRankDensityFloor j)
    (R.selectedRankTolerance j)

/-- Coarse-upper tuples rejected by the selected rankwise thresholds. -/
noncomputable def selectedCoarseBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    Finset (Fin (j.1 + 1) → G) :=
  R.toCoarseFine.orderedCoarseOwnAtomBadBaseSupport
    j e
    (R.selectedRankDensityFloor j)
    (R.selectedRankTolerance j)

/-- Avoidance of the selected coarse-upper bad base gives mixed local
goodness at the literal selected thresholds. -/
theorem selectedCoarseAtomIsGoodAtBoundary_of_not_mem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1))
    (x : Fin (j.1 + 1) → G)
    (hx : x ∉ R.selectedCoarseBadBaseSupport j e) :
    R.SelectedCoarseAtomIsGoodAtBoundary j e x := by
  apply orderedAtomIsGoodAtBoundary_of_not_mem_badBase
  intro hbad
  exact hx
    ((R.toCoarseFine.mem_orderedCoarseOwnAtomBadBaseSupport
      j e
      (R.selectedRankDensityFloor j)
      (R.selectedRankTolerance j) x).2 hbad)

/-- Exact coarse-upper bad-base estimate before inserting the selected
upper-complexity and energy-gap bounds. -/
theorem mean_indicator_selectedCoarseBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    mean (finsetIndicator
        (R.selectedCoarseBadBaseSupport j e)) ≤
      (FacePartition.complexity
          (R.coarse.partition j.succ e) : ℝ) *
          R.selectedRankDensityFloor j +
        R.toCoarseFine.coarseUpperFaceAtomEnergyGap j e /
          R.selectedRankTolerance j := by
  exact
    R.toCoarseFine.mean_indicator_orderedCoarseOwnAtomBadBaseSupport_le
      j e
      (R.selectedRankDensityFloor_nonneg j)
      (R.selectedRankTolerance_pos j)

/-- The coarse-upper bad mass consumes the literal rank tolerance and gap.
The additional fine-upper complexity factor is precisely the cost of
changing the frozen upper atom family from fine to coarse. -/
theorem mean_indicator_selectedCoarseBadBaseSupport_le_selected
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    mean (finsetIndicator
        (R.selectedCoarseBadBaseSupport j e)) ≤
      (R.selectedCoarseUpperComplexityBound j : ℝ) *
          R.selectedRankDensityFloor j +
        ((R.selectedFineUpperComplexityBound j : ℝ) * γ j) /
          R.selectedRankTolerance j := by
  have hface :
      R.toCoarseFine.faceAtomEnergyGap j e ≤ γ j := by
    exact
      (R.toCoarseFine.faceAtomEnergyGap_le_layer j e).trans
        (by
          simpa [toCoarseFine,
            OrderedCoarseFineComplex.layerAtomEnergyGap] using
            R.gap_le j)
  have hcoarseGap :
      R.toCoarseFine.coarseUpperFaceAtomEnergyGap j e ≤
        (R.selectedFineUpperComplexityBound j : ℝ) * γ j := by
    calc
      R.toCoarseFine.coarseUpperFaceAtomEnergyGap j e ≤
          (FacePartition.complexity
              (R.fine.partition j.succ e) : ℝ) *
            R.toCoarseFine.faceAtomEnergyGap j e :=
        R.toCoarseFine.coarseUpperFaceAtomEnergyGap_le j e
      _ ≤
          (R.selectedFineUpperComplexityBound j : ℝ) *
            R.toCoarseFine.faceAtomEnergyGap j e := by
        exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (R.fine_upper_complexity_le_selected j e))
          (R.toCoarseFine.faceAtomEnergyGap_nonneg j e)
      _ ≤
          (R.selectedFineUpperComplexityBound j : ℝ) * γ j := by
        exact mul_le_mul_of_nonneg_left hface
          (Nat.cast_nonneg _)
  exact
    (R.mean_indicator_selectedCoarseBadBaseSupport_le j e).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (R.coarse_upper_complexity_le_selected j e))
          (R.selectedRankDensityFloor_nonneg j))
        (div_le_div_of_nonneg_right hcoarseGap
          (R.selectedRankTolerance_nonneg j)))

/-! ## Rankwise top-face cleaning -/

/-- Fine-upper bad-base deletion family at the selected hierarchical
thresholds. -/
noncomputable def selectedFineBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  orderedBadBaseDeletionFamily
    R.fine R.coarse
    R.selectedDensityFloor
    R.selectedDefectThreshold

/-- Coarse-upper bad-base deletion family at the selected hierarchical
thresholds. -/
noncomputable def selectedCoarseBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  R.toCoarseFine.orderedCoarseBadBaseDeletionFamily
    R.selectedDensityFloor
    R.selectedDefectThreshold

/-- Per-top-face fine-upper cleaning bound with no global collapse of
complexities, tolerances, or gaps. -/
theorem faceDeletionDensity_selectedFineBadBase_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        R.selectedFineBadBaseDeletionFamily e ≤
      ∑ q : OrderedPositiveSubface r,
        ((R.selectedFineUpperComplexityBound q.1 : ℝ) *
            R.selectedRankDensityFloor q.1 +
          γ q.1 /
            R.selectedRankTolerance q.1) := by
  have hbase :=
    faceDeletionDensity_orderedBadBaseDeletionFamily_le
      R.refines
      R.selectedDensityFloor
      R.selectedDefectThreshold
      (fun j => R.selectedDensityFloor_nonneg (j + 1))
      (fun j => R.selectedDefectThreshold_pos (j + 1))
      e
  simp only [selectedDensityFloor_succ,
    selectedDefectThreshold_succ] at hbase
  refine hbase.trans ?_
  apply Finset.sum_le_sum
  intro q _hq
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr
        (R.fine_upper_complexity_le_selected
          q.1 (q.2.trans e)))
      (R.selectedRankDensityFloor_nonneg q.1)
  · apply div_le_div_of_nonneg_right
      ((R.toCoarseFine.faceAtomEnergyGap_le_layer
          q.1 (q.2.trans e)).trans ?_)
      (R.selectedRankTolerance_nonneg q.1)
    simpa [toCoarseFine,
      OrderedCoarseFineComplex.layerAtomEnergyGap] using
      R.gap_le q.1

/-- Per-top-face coarse-upper cleaning bound.  The selected fine-upper
complexity factor appears only in the energy-gap term. -/
theorem faceDeletionDensity_selectedCoarseBadBase_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        R.selectedCoarseBadBaseDeletionFamily e ≤
      ∑ q : OrderedPositiveSubface r,
        ((R.selectedCoarseUpperComplexityBound q.1 : ℝ) *
            R.selectedRankDensityFloor q.1 +
          ((R.selectedFineUpperComplexityBound q.1 : ℝ) * γ q.1) /
            R.selectedRankTolerance q.1) := by
  have hbase :=
    R.toCoarseFine.faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
      R.selectedDensityFloor
      R.selectedDefectThreshold
      (fun j => R.selectedDensityFloor_nonneg (j + 1))
      (fun j => R.selectedDefectThreshold_pos (j + 1))
      e
  simp only [selectedDensityFloor_succ,
    selectedDefectThreshold_succ] at hbase
  refine hbase.trans ?_
  apply Finset.sum_le_sum
  intro q _hq
  have hface :
      R.toCoarseFine.faceAtomEnergyGap
          q.1 (q.2.trans e) ≤ γ q.1 := by
    exact
      (R.toCoarseFine.faceAtomEnergyGap_le_layer
          q.1 (q.2.trans e)).trans
        (by
          simpa [toCoarseFine,
            OrderedCoarseFineComplex.layerAtomEnergyGap] using
            R.gap_le q.1)
  have hcoarseGap :
      R.toCoarseFine.coarseUpperFaceAtomEnergyGap
          q.1 (q.2.trans e) ≤
        (R.selectedFineUpperComplexityBound q.1 : ℝ) *
          γ q.1 := by
    calc
      R.toCoarseFine.coarseUpperFaceAtomEnergyGap
            q.1 (q.2.trans e) ≤
          (FacePartition.complexity
              (R.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
            R.toCoarseFine.faceAtomEnergyGap
              q.1 (q.2.trans e) :=
        R.toCoarseFine.coarseUpperFaceAtomEnergyGap_le
          q.1 (q.2.trans e)
      _ ≤
          (R.selectedFineUpperComplexityBound q.1 : ℝ) *
            R.toCoarseFine.faceAtomEnergyGap
              q.1 (q.2.trans e) := by
        exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (R.fine_upper_complexity_le_selected
              q.1 (q.2.trans e)))
          (R.toCoarseFine.faceAtomEnergyGap_nonneg
            q.1 (q.2.trans e))
      _ ≤
          (R.selectedFineUpperComplexityBound q.1 : ℝ) *
            γ q.1 :=
        mul_le_mul_of_nonneg_left hface (Nat.cast_nonneg _)
  exact add_le_add
    (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr
        (R.coarse_upper_complexity_le_selected
          q.1 (q.2.trans e)))
      (R.selectedRankDensityFloor_nonneg q.1))
    (div_le_div_of_nonneg_right hcoarseGap
      (R.selectedRankTolerance_nonneg q.1))

/-! ## Selected mixed configuration counting -/

/-- A mixed-good closed coarse configuration has the full rankwise lower
bound obtained by using `ρ_j = 1 / log(F(M_j))` for density, `τ_j` for
regularity and the localized square-defect threshold, and `sqrt τ_j` for
the resulting elementary defect error. -/
theorem mixedFullConfigurationCount_lower_bound_selected
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (A : ClosedOrderedAtomConfiguration G k r R.coarse)
    (hgood :
      A.IsMixedGood R.toCoarseFine
        R.selectedDensityFloor
        R.selectedDefectThreshold) :
    (∏ e : PositiveOrderedFace k r,
        R.selectedDensityFloor e.rank) -
      (∑ e : PositiveOrderedFace k r,
        (R.selectedDefectError e.rank +
          (R.selectedFineUpperComplexityBound
              e.lowerRank : ℝ) *
            R.selectedRankTolerance e.lowerRank)) ≤
      fullConfigurationCount A := by
  apply mixedFullConfigurationCount_lower_bound_of_fine
    R.toCoarseFine A
    R.selectedDensityFloor
    R.selectedDefectThreshold
    hgood
    R.selectedRankTolerance
    R.regular_selectedRankTolerance
    R.selectedFineUpperComplexityBound
    R.fine_upper_complexity_le_selected
    R.selectedDefectError
    R.selectedDensityFloor_nonneg
    R.selectedRankTolerance_nonneg
    R.selectedDefectError_nonneg
    R.selectedDefectThreshold_nonneg
  intro n
  exact (R.selectedDefectThreshold_eq_defectError_sq n).le

/-- The corresponding strict rankwise inequality makes every selected
mixed-good coarse configuration occur with positive normalized count. -/
theorem mixedFullConfigurationCount_pos_selected
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (A : ClosedOrderedAtomConfiguration G k r R.coarse)
    (hgood :
      A.IsMixedGood R.toCoarseFine
        R.selectedDensityFloor
        R.selectedDefectThreshold)
    (hsmall :
      (∑ e : PositiveOrderedFace k r,
        (R.selectedDefectError e.rank +
          (R.selectedFineUpperComplexityBound
              e.lowerRank : ℝ) *
            R.selectedRankTolerance e.lowerRank)) <
        ∏ e : PositiveOrderedFace k r,
          R.selectedDensityFloor e.rank) :
    0 < fullConfigurationCount A := by
  have hlower :=
    R.mixedFullConfigurationCount_lower_bound_selected
      A hgood
  linarith

/-! ## Specialized coarse-removal cover -/

/-- The semantic coarse-removal contradiction specialized to the literal
selected hierarchy.  The only remaining hypothesis is the explicit finite
rankwise domination of the original pattern count by the selected counting
lower bound. -/
theorem selectedCoarseBadBaseDeletionFamily_isCover
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    {initialBound : Fin (n + 2) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin (n + 1) → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k (n + 1)
        (orderedPatternInitialComplex H)
        initialBound F γ)
    (hcount :
      H.toWeighted.patternCount <
        (∏ e : PositiveOrderedFace k (n + 1),
          R.selectedDensityFloor e.rank) -
        (∑ e : PositiveOrderedFace k (n + 1),
          (R.selectedDefectError e.rank +
            (R.selectedFineUpperComplexityBound
                e.lowerRank : ℝ) *
              R.selectedRankTolerance e.lowerRank))) :
    H.IsCover R.selectedCoarseBadBaseDeletionFamily := by
  apply
    orderedCoarseBadBaseDeletionFamily_isCover_of_mixedGood_count
      hrk H R.toCoarseFine
      R.coarse_refines_initial
      R.selectedDensityFloor
      R.selectedDefectThreshold
      ((∏ e : PositiveOrderedFace k (n + 1),
          R.selectedDensityFloor e.rank) -
        (∑ e : PositiveOrderedFace k (n + 1),
          (R.selectedDefectError e.rank +
            (R.selectedFineUpperComplexityBound
                e.lowerRank : ℝ) *
              R.selectedRankTolerance e.lowerRank)))
      hcount
  intro A hgood
  exact R.mixedFullConfigurationCount_lower_bound_selected
    A hgood

end GrowthFunctionOrderedComplexRegularityCertificate

end Submission.GreenTao
