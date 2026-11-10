-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.GeneratorCells
import Submission.Hypergraph.WeakCounting

/-!
# Generator-retaining simplex regularization

The weak counting lemma needs only the output partitions.  Recursive
simplex removal needs more: it must retain the bounded list of lower-face
product cuts which generates each partition.  This file packages the
simultaneous regularization with those certificates, starting from the
indiscrete partition in every edge colour.
-/

namespace Submission.GreenTao

/-- The indiscrete regularity state in every edge colour. -/
def indiscreteSimplexRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G] (n : ℕ) :
    SimplexRegularitySystem G n :=
  fun _ => ⟨FacePartition.indiscrete⟩

@[simp]
theorem indiscreteSimplexRegularitySystem_partition
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (j : Fin (n + 1)) :
    (indiscreteSimplexRegularitySystem G n j).partition =
      FacePartition.indiscrete :=
  rfl

/-- All data produced by one simultaneous weak regularization, including
the actual lower-face generators. -/
structure GeneratedSimplexRegularization
    (G : Type*) [Fintype G] [DecidableEq G] (n : ℕ)
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (ε : ℝ) where
  state : SimplexRegularitySystem G n
  generators :
    (j : Fin (n + 1)) →
      Finset (BooleanCutTest (Fin n → G))
  budgetLength : Fin (n + 1) → ℕ
  stepIndex : Fin (n + 1) → ℕ
  budget_large :
    ∀ j, 1 < (budgetLength j : ℝ) * ε ^ 2
  step_lt_budget :
    ∀ j, stepIndex j < budgetLength j
  partition_eq_generated :
    ∀ j, (state j).partition =
      FacePartition.generatedBy (generators j)
  generators_supported :
    ∀ j, generators j ⊆ booleanFaceCutSupports G n
  generator_card_le :
    ∀ j, (generators j).card ≤ stepIndex j
  regular :
    ∀ j, (state j).IsFaceCutRegular
      (canonicalEdgeFunction H j) ε
  count_close :
    |H.simplexCount -
        (regularizedSimplexSystem H state).simplexCount| ≤
      ((n + 1 : ℕ) : ℝ) * ε
  complexity_le :
    ∀ j, FacePartition.complexity (state j).partition ≤
      2 ^ stepIndex j

/-- Simultaneous weak regularization from indiscrete partitions, retaining
all generator data and the exact counting conclusion. -/
theorem exists_generatedSimplexRegularization
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ} (hn : 0 < n)
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (GeneratedSimplexRegularization G n H ε) := by
  classical
  let S₀ := indiscreteSimplexRegularitySystem G n
  have hj (j : Fin (n + 1)) :
      ∃ m i : ℕ,
        ∃ T : FaceRegularityState (Fin n → G),
        ∃ F : Finset (BooleanCutTest (Fin n → G)),
          1 < (m : ℝ) * ε ^ 2 ∧
          i < m ∧
          T.partition =
            FacePartition.join (S₀ j).partition
              (FacePartition.generatedBy F) ∧
          F ⊆ booleanFaceCutSupports G n ∧
          F.card ≤ i ∧
          T.IsFaceCutRegular
            (canonicalEdgeFunction H j) ε ∧
          FacePartition.complexity T.partition ≤
            2 ^ i *
              FacePartition.complexity (S₀ j).partition := by
    exact
      (S₀ j).exists_faceCutRegular_refinement_with_generators
        hn (canonicalEdgeFunction H j)
        (canonicalEdgeFunction_nonneg hH j)
        (canonicalEdgeFunction_le_one hH j) hε
  choose m i S F hdata using hj
  have hbudget :
      ∀ j, 1 < (m j : ℝ) * ε ^ 2 := by
    intro j
    exact (hdata j).1
  have hstep :
      ∀ j, i j < m j := by
    intro j
    exact (hdata j).2.1
  have hpartition :
      ∀ j, (S j).partition =
        FacePartition.generatedBy (F j) := by
    intro j
    have h := (hdata j).2.2.1
    simpa [S₀, indiscreteSimplexRegularitySystem,
      FacePartition.join, FacePartition.indiscrete] using h
  have hsupported :
      ∀ j, F j ⊆ booleanFaceCutSupports G n := by
    intro j
    exact (hdata j).2.2.2.1
  have hcard :
      ∀ j, (F j).card ≤ i j := by
    intro j
    exact (hdata j).2.2.2.2.1
  have hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε := by
    intro j
    exact (hdata j).2.2.2.2.2.1
  have hcomplexity :
      ∀ j, FacePartition.complexity (S j).partition ≤
        2 ^ i j := by
    intro j
    have h := (hdata j).2.2.2.2.2.2
    simpa [S₀, indiscreteSimplexRegularitySystem] using h
  exact
    ⟨{
      state := S
      generators := F
      budgetLength := m
      stepIndex := i
      budget_large := hbudget
      step_lt_budget := hstep
      partition_eq_generated := hpartition
      generators_supported := hsupported
      generator_card_le := hcard
      regular := hregular
      count_close :=
        simplexCount_abs_sub_regularized_le
          H hH S hregular
      complexity_le := hcomplexity
    }⟩

namespace GeneratedSimplexRegularization

/-- A simultaneous branch choice for every top edge colour. -/
abbrev BranchSystem
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε) :=
  (j : Fin (n + 1)) → GeneratorBranch (R.generators j)

@[simp]
theorem card_branchSystem
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε) :
    Fintype.card R.BranchSystem =
      ∏ j, n ^ (R.generators j).card := by
  simp [BranchSystem]

/-- A branch system has an ambient-size-independent cardinality bound in
terms of the regularity step indices. -/
theorem card_branchSystem_le
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (hn : 0 < n) :
    Fintype.card R.BranchSystem ≤
      ∏ j, n ^ R.stepIndex j := by
  rw [R.card_branchSystem]
  apply Finset.prod_le_prod₀
  · intro j _hj
    exact Nat.zero_le _
  · intro j _hj
    exact
      Nat.pow_le_pow_right hn
        (R.generator_card_le j)

/-- One choice of a structured top atom in every edge colour. -/
abbrev TopAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε) :=
  (j : Fin (n + 1)) → (R.state j).partition.parts

@[simp]
theorem card_topAtomChoice
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε) :
    Fintype.card R.TopAtomChoice =
      ∏ j, FacePartition.complexity
        (R.state j).partition := by
  simp [TopAtomChoice, FacePartition.complexity]

/-- The number of simultaneous top-atom choices is bounded solely by the
regularity step indices. -/
theorem card_topAtomChoice_le
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε) :
    Fintype.card R.TopAtomChoice ≤
      ∏ j, 2 ^ R.stepIndex j := by
  rw [R.card_topAtomChoice]
  apply Finset.prod_le_prod₀
  · intro j _hj
    exact Nat.zero_le _
  · intro j _hj
    exact R.complexity_le j

/-- The simultaneous atom choice occupied by a full vertex tuple. -/
noncomputable def topAtomChoiceOf
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (x : Fin (n + 1) → G) :
    R.TopAtomChoice :=
  fun j =>
    ⟨(R.state j).partition.part
        (deletedFaceTuple j (deleteCoordinate x j)),
      (R.state j).partition.part_mem.2
        (Finset.mem_univ _)⟩

/-- A tuple realizes precisely the top atoms selected by `topAtomChoiceOf`.
-/
theorem mem_topAtomChoiceOf
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (x : Fin (n + 1) → G) (j : Fin (n + 1)) :
    deletedFaceTuple j (deleteCoordinate x j) ∈
      (R.topAtomChoiceOf x j).1 := by
  exact
    (R.state j).partition.mem_part
      (Finset.mem_univ _)

/-- Membership in the product of lower-face cells selected for every top
edge of a reference simplex tuple. -/
def IsInCell
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (reference : Fin (n + 1) → G)
    (w : R.BranchSystem)
    (x : Fin (n + 1) → G) : Prop :=
  ∀ j i,
    eraseCoordinate i
        (deletedFaceTuple j (deleteCoordinate x j)) ∈
      lowerGeneratorCell (R.generators j)
        (deletedFaceTuple j
          (deleteCoordinate reference j))
        (w j) i

/-- The atom certificate for one edge colour, transported from its
generator partition to the actual regularity state. -/
theorem mem_state_part_iff_exists_lowerGeneratorCells
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (hn : 0 < n) (j : Fin (n + 1))
    (y x : Fin n → G) :
    x ∈ (R.state j).partition.part y ↔
      ∃ w : GeneratorBranch (R.generators j),
        ∀ i,
          eraseCoordinate i x ∈
            lowerGeneratorCell (R.generators j) y w i := by
  rw [R.partition_eq_generated j]
  exact
    mem_generatedBy_part_iff_exists_lowerGeneratorCells
      hn (R.generators j)
        (R.generators_supported j) y x

/-- Two full tuples occupy the same structured top cells in every colour
exactly when one simultaneous lower-face branch system accepts the second
tuple. -/
theorem same_top_atoms_iff_exists_branchSystem
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (hn : 0 < n)
    (reference x : Fin (n + 1) → G) :
    (∀ j,
      deletedFaceTuple j (deleteCoordinate x j) ∈
        (R.state j).partition.part
          (deletedFaceTuple j
            (deleteCoordinate reference j))) ↔
      ∃ w : R.BranchSystem, R.IsInCell reference w x := by
  classical
  constructor
  · intro hsame
    have hj (j : Fin (n + 1)) :
        ∃ w : GeneratorBranch (R.generators j),
          ∀ i,
            eraseCoordinate i
                (deletedFaceTuple j
                  (deleteCoordinate x j)) ∈
              lowerGeneratorCell (R.generators j)
                (deletedFaceTuple j
                  (deleteCoordinate reference j))
                w i :=
      (R.mem_state_part_iff_exists_lowerGeneratorCells
        hn j _ _).1 (hsame j)
    choose w hw using hj
    exact ⟨w, fun j i => hw j i⟩
  · rintro ⟨w, hcell⟩
    intro j
    exact
      (R.mem_state_part_iff_exists_lowerGeneratorCells
        hn j _ _).2 ⟨w j, hcell j⟩

/-- A regularized edge weight is constant on the corresponding generated
top cell. -/
theorem regularized_edgeWeight_eq_of_mem_state_part
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (j : Fin (n + 1))
    (reference x : Fin (n + 1) → G)
    (hmem :
      deletedFaceTuple j (deleteCoordinate x j) ∈
        (R.state j).partition.part
          (deletedFaceTuple j
            (deleteCoordinate reference j))) :
    (regularizedSimplexSystem H R.state).edgeWeight j
        (deleteCoordinate x j) =
      (regularizedSimplexSystem H R.state).edgeWeight j
        (deleteCoordinate reference j) := by
  exact
    conditionalMean_eq_of_mem_part
      (R.state j).partition (canonicalEdgeFunction H j) hmem

/-- Consequently, the entire regularized simplex weight is constant on a
simultaneous branch cell. -/
theorem regularized_simplexWeight_eq_of_isInCell
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (R : GeneratedSimplexRegularization G n H ε)
    (hn : 0 < n)
    (reference x : Fin (n + 1) → G)
    (w : R.BranchSystem)
    (hcell : R.IsInCell reference w x) :
    (regularizedSimplexSystem H R.state).simplexWeight x =
      (regularizedSimplexSystem H R.state).simplexWeight
        reference := by
  have hsame :=
    (R.same_top_atoms_iff_exists_branchSystem
      hn reference x).2 ⟨w, hcell⟩
  apply Finset.prod_congr rfl
  intro j _hj
  exact
    R.regularized_edgeWeight_eq_of_mem_state_part
      j reference x (hsame j)

end GeneratedSimplexRegularization

end Submission.GreenTao
