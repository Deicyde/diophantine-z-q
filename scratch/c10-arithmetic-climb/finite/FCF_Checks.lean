/-
FINITE COEFFICIENT FIELD — CONFORMANCE/POSITIVES/AXIOM CHECK SOURCE v1.
Not yet executed here; execution is sole ParentA, not the source-author child.
F1-F6 types below are verbatim expressions extracted from frozen target
66c85645fd3a4b4036208be83910661b45a903e6f443d87e31100fc923d405f0.
These are type assignments to actual proved declarations, not assumed predicates.
Positives use only GIVEN coefficients/matrices and explicit finite index types.
No distinct coefficient-count assertion or concrete nonrational witness is made.
-/

import FCF_Proof

noncomputable section
universe u v w

namespace ClimbFiniteCoefficientFieldChecks
open ClimbFiniteCoefficientField

-- F1: verbatim frozen type, no new expected predicate.
example :
  (∀ (s : Set Qbar) (_hs : s.Finite), FiniteDimensional ℚ (fieldOf s)) :=
  finiteDimensional_fieldOf

-- F2: verbatim frozen type, no new expected predicate.
example :
  (∀ (s : Set Qbar) (_hs : s.Finite), NumberField (fieldOf s)) :=
  numberField_fieldOf

-- F3: verbatim frozen type, no new expected predicate.
example :
  (∀ (s : Set Qbar) (_hs : s.Finite) (ρ : Qbar →ₐ[ℚ] ℂ),
    let E : IntermediateField ℚ Qbar := fieldOf s
    let ρE : E →ₐ[ℚ] ℂ := restrictedPlace s ρ
    FiniteDimensional ℚ E ∧
    NumberField E ∧
    (s ⊆ (E : Set Qbar)) ∧
    (∀ F : IntermediateField ℚ Qbar, s ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (coefficientLift s a) = a.1 ∧
      ρE (coefficientLift s a) = ρ a.1) ∧
    ρE.fieldRange = E.map ρ) :=
  finiteSet_numberField_fixedPlace

-- F4: verbatim frozen type, no new expected predicate.
example :
  (∀ {ι : Sort u} [Finite ι] (c : ι → Qbar) (ρ : Qbar →ₐ[ℚ] ℂ),
    FiniteDimensional ℚ (familyField c) ∧
    NumberField (familyField c) ∧
    (∀ i : ι,
      (familyField c).val (familyLift c i) = c i ∧
      familyPlace c ρ (familyLift c i) = ρ (c i)) ∧
    Set.range (fun i : ι => familyPlace c ρ (familyLift c i)) =
      Set.range (fun i : ι => ρ (c i))) :=
  finiteFamily_numberField_fixedPlace

-- F5: verbatim frozen type, no new expected predicate.
example :
  (∀ {κ : Type u} (Row : κ → Type v) (Col : κ → Type w)
    [Finite κ] [∀ k : κ, Finite (Row k)] [∀ k : κ, Finite (Col k)]
    (s : Set Qbar) (_hs : s.Finite)
    (M : (k : κ) → Matrix (Row k) (Col k) Qbar) (ρ : Qbar →ₐ[ℚ] ℂ),
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
      ρE (jointMatrixLift s M k i j) = ρ (M k i j))) :=
  finiteScalars_and_matrixFamily_oneField

-- F6: verbatim frozen type, no new expected predicate.
example :
  (∀ (s : Set Qbar) (ρ : Qbar →+* ℂ),
    (∀ x : fieldOf s, restrictedRingPlace s ρ x = ρ ((fieldOf s).val x)) ∧
    (∀ a : s,
      restrictedRingPlace s ρ (coefficientLift s a) = ρ a.1) ∧
    Set.range (restrictedRingPlace s ρ) = ρ '' (fieldOf s : Set Qbar)) :=
  restrictedRingPlace_compatible

/-- Empty generating set, actual adjoin, and unchanged caller place. -/
theorem PEmptySet (ρ : Qbar →ₐ[ℚ] ℂ) :
    let E : IntermediateField ℚ Qbar := fieldOf (∅ : Set Qbar)
    let ρE : E →ₐ[ℚ] ℂ := restrictedPlace (∅ : Set Qbar) ρ
    FiniteDimensional ℚ E ∧ NumberField E ∧
    ((∅ : Set Qbar) ⊆ (E : Set Qbar)) ∧
    (∀ F : IntermediateField ℚ Qbar, (∅ : Set Qbar) ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : (∅ : Set Qbar),
      E.val (coefficientLift (∅ : Set Qbar) a) = a.1 ∧
      ρE (coefficientLift (∅ : Set Qbar) a) = ρ a.1) ∧
    ρE.fieldRange = E.map ρ :=
  finiteSet_numberField_fixedPlace (∅ : Set Qbar) Set.finite_empty ρ

/-- The GIVEN a is repeated three times; all indices, not three distinct values. -/
theorem PRepeated (a : Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    let c : Fin 3 → Qbar := fun _ => a
    FiniteDimensional ℚ (familyField c) ∧ NumberField (familyField c) ∧
    (∀ i : Fin 3,
      (familyField c).val (familyLift c i) = c i ∧
      familyPlace c ρ (familyLift c i) = ρ (c i)) ∧
    Set.range (fun i : Fin 3 => familyPlace c ρ (familyLift c i)) =
      Set.range (fun i : Fin 3 => ρ (c i)) :=
  finiteFamily_numberField_fixedPlace (fun _ : Fin 3 => a) ρ

/-- GIVEN matrices with varying finite dimensions; every k/i/j in the full result. -/
theorem PVaryingMatrices (s : Set Qbar) (hs : s.Finite)
    (M : (k : Fin 2) → Matrix (Fin (k.val + 1)) (Fin (k.val + 2)) Qbar)
    (ρ : Qbar →ₐ[ℚ] ℂ) :
    let t : Set Qbar := jointSet s M
    let E : IntermediateField ℚ Qbar := jointField s M
    let ρE : E →ₐ[ℚ] ℂ := jointPlace s M ρ
    t.Finite ∧ FiniteDimensional ℚ E ∧ NumberField E ∧
    (∀ F : IntermediateField ℚ Qbar, t ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (jointScalarLift s M a) = a.1 ∧
      ρE (jointScalarLift s M a) = ρ a.1) ∧
    (∀ (k : Fin 2) (i : Fin (k.val + 1)) (j : Fin (k.val + 2)),
      E.val (jointMatrixLift s M k i j) = M k i j ∧
      ρE (jointMatrixLift s M k i j) = ρ (M k i j)) :=
  finiteScalars_and_matrixFamily_oneField
    (fun k : Fin 2 => Fin (k.val + 1)) (fun k : Fin 2 => Fin (k.val + 2)) s hs M ρ

/-- Empty GIVEN matrix family; no Nonempty family premise. -/
theorem PEmptyMatrixFamily (s : Set Qbar) (hs : s.Finite)
    (M : (k : Fin 0) → Matrix (Fin 2) (Fin 2) Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    let t : Set Qbar := jointSet s M
    let E : IntermediateField ℚ Qbar := jointField s M
    let ρE : E →ₐ[ℚ] ℂ := jointPlace s M ρ
    t.Finite ∧ FiniteDimensional ℚ E ∧ NumberField E ∧
    (∀ F : IntermediateField ℚ Qbar, t ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (jointScalarLift s M a) = a.1 ∧
      ρE (jointScalarLift s M a) = ρ a.1) ∧
    (∀ (k : Fin 0) (i : Fin 2) (j : Fin 2),
      E.val (jointMatrixLift s M k i j) = M k i j ∧
      ρE (jointMatrixLift s M k i j) = ρ (M k i j)) :=
  finiteScalars_and_matrixFamily_oneField
    (fun _ : Fin 0 => Fin 2) (fun _ : Fin 0 => Fin 2) s hs M ρ

/-- GIVEN matrices with zero rows; no hidden Nonempty row premise. -/
theorem PZeroRows (s : Set Qbar) (hs : s.Finite)
    (M : (k : Fin 1) → Matrix (Fin 0) (Fin 2) Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    let t : Set Qbar := jointSet s M
    let E : IntermediateField ℚ Qbar := jointField s M
    let ρE : E →ₐ[ℚ] ℂ := jointPlace s M ρ
    t.Finite ∧ FiniteDimensional ℚ E ∧ NumberField E ∧
    (∀ F : IntermediateField ℚ Qbar, t ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (jointScalarLift s M a) = a.1 ∧
      ρE (jointScalarLift s M a) = ρ a.1) ∧
    (∀ (k : Fin 1) (i : Fin 0) (j : Fin 2),
      E.val (jointMatrixLift s M k i j) = M k i j ∧
      ρE (jointMatrixLift s M k i j) = ρ (M k i j)) :=
  finiteScalars_and_matrixFamily_oneField
    (fun _ : Fin 1 => Fin 0) (fun _ : Fin 1 => Fin 2) s hs M ρ

/-- GIVEN matrices with zero columns; no hidden Nonempty column premise. -/
theorem PZeroColumns (s : Set Qbar) (hs : s.Finite)
    (M : (k : Fin 1) → Matrix (Fin 2) (Fin 0) Qbar) (ρ : Qbar →ₐ[ℚ] ℂ) :
    let t : Set Qbar := jointSet s M
    let E : IntermediateField ℚ Qbar := jointField s M
    let ρE : E →ₐ[ℚ] ℂ := jointPlace s M ρ
    t.Finite ∧ FiniteDimensional ℚ E ∧ NumberField E ∧
    (∀ F : IntermediateField ℚ Qbar, t ⊆ (F : Set Qbar) → E ≤ F) ∧
    (∀ a : s,
      E.val (jointScalarLift s M a) = a.1 ∧
      ρE (jointScalarLift s M a) = ρ a.1) ∧
    (∀ (k : Fin 1) (i : Fin 2) (j : Fin 0),
      E.val (jointMatrixLift s M k i j) = M k i j ∧
      ρE (jointMatrixLift s M k i j) = ρ (M k i j)) :=
  finiteScalars_and_matrixFamily_oneField
    (fun _ : Fin 1 => Fin 2) (fun _ : Fin 1 => Fin 0) s hs M ρ

end ClimbFiniteCoefficientFieldChecks

#check @ClimbFiniteCoefficientField.finiteDimensional_fieldOf
#check @ClimbFiniteCoefficientField.numberField_fieldOf
#check @ClimbFiniteCoefficientField.finiteSet_numberField_fixedPlace
#check @ClimbFiniteCoefficientField.finiteFamily_numberField_fixedPlace
#check @ClimbFiniteCoefficientField.finiteScalars_and_matrixFamily_oneField
#check @ClimbFiniteCoefficientField.restrictedRingPlace_compatible

#print axioms ClimbFiniteCoefficientField.finiteDimensional_fieldOf
#print axioms ClimbFiniteCoefficientField.numberField_fieldOf
#print axioms ClimbFiniteCoefficientField.finiteSet_numberField_fixedPlace
#print axioms ClimbFiniteCoefficientField.finiteFamily_numberField_fixedPlace
#print axioms ClimbFiniteCoefficientField.finiteScalars_and_matrixFamily_oneField
#print axioms ClimbFiniteCoefficientField.restrictedRingPlace_compatible
