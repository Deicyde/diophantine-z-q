/-
FINITE GIVEN COEFFICIENTS — PROOF SOURCE v1, NOT YET COMPILED.

Author: child finite-coefficient-field lane on owned OD scratch.
Executor: parent a23, sole-occupant fresh worker A. No child compiler.

Imports the ACTUAL module name produced by the parent DEF gate from frozen
source SHA256 66c85645fd3a4b4036208be83910661b45a903e6f443d87e31100fc923d405f0.
All six theorem types reproduce the already frozen F1-F6 expressions.
No frozen definition, coefficient value, place, universe or index is changed.
No CommonCoefficientField/fieldExists predicate or assumed FD result is used.
No C10, finite Tate image, topology, or original arithmetic object is claimed.
-/

import FiniteCoefficientFieldTarget

noncomputable section

universe u v w

namespace ClimbFiniteCoefficientField

/-- F1: the given finite generators are integral in Qbar; reuse Mathlib. -/
theorem finiteDimensional_fieldOf (s : Set Qbar) (hs : s.Finite) :
    FiniteDimensional ℚ (fieldOf s) := by
  letI : Finite s := hs.to_subtype
  exact IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := s)
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)

/-- F2: derive NumberField from F1, never use it as an input to F1. -/
theorem numberField_fieldOf (s : Set Qbar) (hs : s.Finite) :
    NumberField (fieldOf s) := by
  letI : FiniteDimensional ℚ (fieldOf s) := finiteDimensional_fieldOf s hs
  exact NumberField.of_module_finite ℚ (fieldOf s)

/-- F3: one literal least adjoin, original values, and the same restricted ρ. -/
theorem finiteSet_numberField_fixedPlace
    (s : Set Qbar) (hs : s.Finite) (ρ : Qbar →ₐ[ℚ] ℂ) :
    let E : IntermediateField ℚ Qbar := fieldOf s
    let ρE : E →ₐ[ℚ] ℂ := restrictedPlace s ρ
    FiniteDimensional ℚ E ∧
    NumberField E ∧
    (s ⊆ (E : Set Qbar)) ∧
    (∀ F : IntermediateField ℚ Qbar, s ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (coefficientLift s a) = a.1 ∧
      ρE (coefficientLift s a) = ρ a.1) ∧
    ρE.fieldRange = E.map ρ := by
  dsimp only
  refine ⟨finiteDimensional_fieldOf s hs, numberField_fieldOf s hs,
    IntermediateField.subset_adjoin ℚ s, ?_, ?_, ?_⟩
  · intro F hF
    exact IntermediateField.adjoin_le_iff.mpr hF
  · intro a
    exact ⟨rfl, rfl⟩
  · simpa only [restrictedPlace] using
      (IntermediateField.fieldRange_comp_val (fieldOf s) ρ)

/-- F4: finite Sort-indexed given family; repetitions and empty families remain. -/
theorem finiteFamily_numberField_fixedPlace
    {ι : Sort u} [Finite ι] (c : ι → Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    FiniteDimensional ℚ (familyField c) ∧
    NumberField (familyField c) ∧
    (∀ i : ι,
      (familyField c).val (familyLift c i) = c i ∧
      familyPlace c ρ (familyLift c i) = ρ (c i)) ∧
    Set.range (fun i : ι => familyPlace c ρ (familyLift c i)) =
      Set.range (fun i : ι => ρ (c i)) := by
  have hs : (Set.range c).Finite := Set.finite_range c
  refine ⟨finiteDimensional_fieldOf (Set.range c) hs,
    numberField_fieldOf (Set.range c) hs, ?_, ?_⟩
  · intro i
    exact ⟨rfl, rfl⟩
  · rfl

/-- F5: ONE E covers every given scalar and every supplied matrix coordinate. -/
theorem finiteScalars_and_matrixFamily_oneField
    {κ : Type u} (Row : κ → Type v) (Col : κ → Type w)
    [Finite κ] [∀ k : κ, Finite (Row k)] [∀ k : κ, Finite (Col k)]
    (s : Set Qbar) (hs : s.Finite)
    (M : (k : κ) → Matrix (Row k) (Col k) Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    let t : Set Qbar := jointSet s M
    let E : IntermediateField ℚ Qbar := jointField s M
    let ρE : E →ₐ[ℚ] ℂ := jointPlace s M ρ
    t.Finite ∧
    FiniteDimensional ℚ E ∧
    NumberField E ∧
    (∀ F : IntermediateField ℚ Qbar, t ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (jointScalarLift s M a) = a.1 ∧
      ρE (jointScalarLift s M a) = ρ a.1) ∧
    (∀ (k : κ) (i : Row k) (j : Col k),
      E.val (jointMatrixLift s M k i j) = M k i j ∧
      ρE (jointMatrixLift s M k i j) = ρ (M k i j)) := by
  have ht : (jointSet s M).Finite :=
    hs.union (Set.finite_range (matrixCoefficient M))
  dsimp only
  refine ⟨ht, finiteDimensional_fieldOf (jointSet s M) ht,
    numberField_fieldOf (jointSet s M) ht, ?_, ?_, ?_⟩
  · intro F hF
    exact IntermediateField.adjoin_le_iff.mpr hF
  · intro a
    exact ⟨rfl, rfl⟩
  · intro k i j
    exact ⟨rfl, rfl⟩

/-- F6: ring-place compatibility for any set; not a finite-field claim. -/
theorem restrictedRingPlace_compatible (s : Set Qbar) (ρ : Qbar →+* ℂ) :
    (∀ x : fieldOf s, restrictedRingPlace s ρ x = ρ ((fieldOf s).val x)) ∧
    (∀ a : s,
      restrictedRingPlace s ρ (coefficientLift s a) = ρ a.1) ∧
    Set.range (restrictedRingPlace s ρ) = ρ '' (fieldOf s : Set Qbar) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rfl
  · intro a
    rfl
  · apply Set.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := hz
      exact ⟨(x : Qbar), x.2, hx⟩
    · intro hz
      obtain ⟨x, hx, he⟩ := hz
      exact ⟨⟨x, hx⟩, he⟩

end ClimbFiniteCoefficientField
