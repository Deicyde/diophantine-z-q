import ZInQKernel.Contrib.TYZGenus.RingClass
open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.TYZGenus.RingClass

section Galois
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem comap_val_lift {E : IntermediateField K L} (F : IntermediateField K E) :
    (IntermediateField.lift F).comap E.val = F := by
  ext x
  simp [IntermediateField.mem_comap, IntermediateField.mem_lift]

theorem finrank_lift {E : IntermediateField K L} (F : IntermediateField K E) :
    Module.finrank K (IntermediateField.lift F) = Module.finrank K F :=
  (IntermediateField.liftAlgEquiv F).toLinearEquiv.finrank_eq.symm

theorem relfinrank_lift {E : IntermediateField K L} (F : IntermediateField K E) :
    (IntermediateField.lift F).relfinrank E = Module.finrank F E := by
  have h := IntermediateField.finrank_comap (IntermediateField.lift F) E.val
  rw [IntermediateField.fieldRange_val, comap_val_lift] at h
  exact h.symm

theorem relfinrank_lift_fixedField {E : IntermediateField K L} [FiniteDimensional K E]
    (H : Subgroup Gal(E/K)) :
    (IntermediateField.lift (IntermediateField.fixedField H)).relfinrank E = Nat.card H := by
  rw [relfinrank_lift, IntermediateField.finrank_fixedField_eq_card]

theorem finrank_lift_fixedField_mul {E : IntermediateField K L} [FiniteDimensional K E]
    (H : Subgroup Gal(E/K)) :
    Module.finrank K (IntermediateField.lift (IntermediateField.fixedField H)) * Nat.card H =
      Module.finrank K E := by
  rw [finrank_lift, ← IntermediateField.finrank_fixedField_eq_card H, Module.finrank_mul_finrank]

end Galois

section Genus
variable {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)

theorem card_picSquares_map :
    Nat.card ((picSquares O).map (ringClassArtinEquiv O).toMonoidHom) = Nat.card (picSquares O) :=
  Nat.card_congr ((picSquares O).equivMapOfInjective _ (ringClassArtinEquiv O).injective).toEquiv.symm

theorem genusField_le : genusField O ≤ ringClassField O := IntermediateField.lift_le _

theorem relfinrank_genusField :
    (genusField O).relfinrank (ringClassField O) = Nat.card (picSquares O) := by
  rw [genusField, relfinrank_lift_fixedField, card_picSquares_map]

theorem finrank_genusField_mul :
    Module.finrank K (genusField O) * Nat.card (picSquares O) = Nat.card (Pic O) := by
  rw [← card_picSquares_map, genusField, finrank_lift_fixedField_mul, finrank_ringClassField]

theorem card_picTwoTorsion_mul : Nat.card (picTwoTorsion O) * Nat.card (picSquares O) = Nat.card (Pic O) :=
  Subgroup.card_ker_mul_card_range _

theorem finrank_genusField : Module.finrank K (genusField O) = Nat.card (picTwoTorsion O) := by
  have h1 := finrank_genusField_mul O
  have h2 := card_picTwoTorsion_mul O
  have hpos : 0 < Nat.card (picSquares O) := Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem finrankGenusField : FinrankGenusField := fun _ _ _ O => ⟨finrank_genusField O, finrank_genusField_mul O⟩

theorem finrankH4 : FinrankH4 := fun d _ => finrank_ringClassField _

end Genus

theorem gCl_eq_card_picSquares (e : ℕ) [NeZero e] :
    ZInQ.RouteK.Rank5b.gCl e = Nat.card (picSquares (maximalNumberFieldOrder (ZInQ.RouteK.Rank5b.QNeg e))) := rfl

end ZInQ.Contrib.TYZGenus.RingClass
