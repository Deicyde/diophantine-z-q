import ZInQKernel.Contrib.DifferentBound.Global
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import ZInQKernel.Contrib.GlobalDifferentTransport.FixedFieldTransport

/-!
# A finite Galois fixed-field presentation of every number field

The ambient field is the normal closure of the given number field inside its
actual algebraic closure. The given field embeds into it by the canonical
normal-closure inclusion. Its image is identified, through the proved finite
Galois correspondence, with the fixed field of its fixing subgroup. This
construction adds no Galois, algebraic-closedness or completion hypothesis to
the given global number field.
-/

namespace ZInQ.Contrib.DifferentBound.Presentation

noncomputable section

open NumberField IntermediateField

variable (L : Type*) [Field L] [NumberField L]

/-- The actual finite normal closure of L/Q in the actual algebraic closure of L. -/
noncomputable abbrev ambient := IntermediateField.normalClosure ℚ L (AlgebraicClosure L)

/-- The ambient field is a number field, by finiteness of the actual normal closure. -/
theorem ambient_numberField : NumberField (ambient L) where
  to_charZero := inferInstance
  to_finiteDimensional := normalClosure.is_finiteDimensional ℚ L (AlgebraicClosure L)

/-- Characteristic-zero separability and normality of the actual closure prove it is Galois. -/
theorem ambient_isGalois : IsGalois ℚ (ambient L) := by
  let : Algebra.IsAlgebraic ℚ L := NumberField.isAlgebraic L
  let : IsAlgClosure ℚ (AlgebraicClosure L) :=
    ⟨AlgebraicClosure.isAlgClosed L, Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)⟩
  let : Normal ℚ (AlgebraicClosure L) := IsAlgClosure.normal ℚ (AlgebraicClosure L)
  let : Algebra.IsSeparable ℚ L := inferInstance
  exact IsGalois.normalClosure_of_isSeparable ℚ L (AlgebraicClosure L)

local instance : NumberField (ambient L) := ambient_numberField L
local instance : IsGalois ℚ (ambient L) := ambient_isGalois L

/-- The given field's actual canonical inclusion into its finite normal closure. -/
noncomputable def embedding : L →ₐ[ℚ] ambient L := IsScalarTower.toAlgHom ℚ L (ambient L)

/-- The actual image of the given field, as an intermediate field of its finite Galois closure. -/
def imageField : IntermediateField ℚ (ambient L) := (embedding L).fieldRange

/-- The subgroup that fixes the actual image, without assuming the original field is Galois. -/
def subgroup : Subgroup Gal(ambient L/ℚ) := (imageField L).fixingSubgroup

/-- The actual rational algebra isomorphism from the given field to its fixed-field presentation. -/
noncomputable def equiv : L ≃ₐ[ℚ] GlobalDifferentTransport.originalFixedField (ambient L) (subgroup L) :=
  (embedding L).equivFieldRange.trans
    (IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup (imageField L)).symm)

/-- The image of the original field is exactly the fixed field used by the arithmetic supplier. -/
theorem fixedField_eq_image :
    GlobalDifferentTransport.originalFixedField (ambient L) (subgroup L) = imageField L :=
  IsGalois.fixedField_fixingSubgroup (imageField L)

#check @ambient_numberField
#check @ambient_isGalois
#check @equiv
#print axioms ambient_numberField
#print axioms ambient_isGalois
#print axioms equiv

end

end ZInQ.Contrib.DifferentBound.Presentation
