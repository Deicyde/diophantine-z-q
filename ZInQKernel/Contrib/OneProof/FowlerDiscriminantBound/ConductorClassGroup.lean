module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.RayClass
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.ClassNumber

/-!
# Extension of ideal classes from an order to its maximal order

This is the global class-group step in Cox, Theorem 7.24. At the conductor modulus the
extension map factors through the Picard group of the order. The remaining factor in the
class-number formula is the kernel of the resulting residue-to-Picard map.
-/

public section

open NumberField TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace HDec.CMBranch.FowlerArithmetic

variable {K : Type*} [Field K] [NumberField K]

private theorem ker_rayClassToPic_le (O : NumberFieldOrder K) :
    O.rayClassToPic.ker ≤ (rayClassToClassGroup O.conductorModulus).ker := by
  intro c hc
  obtain ⟨J, rfl, β, _, hJ⟩ := O.mem_ker_rayClassToPic.mp hc
  rw [MonoidHom.mem_ker, idealClass_apply, rayClassToClassGroup_rayClassMk]
  refine ClassGroup.mk_eq_one_iff.mpr ?_
  rw [TauCeti.NumberFieldArithmetic.coe_integralIdealsAwayHom]
  apply (IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) _).mpr
  rw [hJ]
  infer_instance

/-- Extend the ideal class of the given order to the ordinary ideal class of its field. -/
noncomputable def orderPicToClassGroup (O : NumberFieldOrder K) : Pic O →* ClassGroup (𝓞 K) :=
  (QuotientGroup.lift O.rayClassToPic.ker (rayClassToClassGroup O.conductorModulus)
    (ker_rayClassToPic_le O)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _ O.rayClassToPic_surjective).symm.toMonoidHom

@[simp] theorem orderPicToClassGroup_rayClassToPic (O : NumberFieldOrder K)
    (c : RayClassGroup O.conductorModulus) :
    orderPicToClassGroup O (O.rayClassToPic c) = rayClassToClassGroup O.conductorModulus c := by
  let e := QuotientGroup.quotientKerEquivOfSurjective _ O.rayClassToPic_surjective
  have he : e.symm (O.rayClassToPic c) = QuotientGroup.mk c :=
    (MulEquiv.symm_apply_eq e).mpr rfl
  change QuotientGroup.lift _ (rayClassToClassGroup O.conductorModulus)
    (ker_rayClassToPic_le O) (e.symm (O.rayClassToPic c)) = _
  rw [he, QuotientGroup.lift_mk]

/-- Every maximal-order ideal class comes from the given order. -/
theorem orderPicToClassGroup_surjective (O : NumberFieldOrder K) :
    Function.Surjective (orderPicToClassGroup O) := by
  intro a
  obtain ⟨c, rfl⟩ := rayClassToClassGroup_surjective O.conductorModulus a
  exact ⟨O.rayClassToPic c, orderPicToClassGroup_rayClassToPic O c⟩

/-- The residue map at the conductor followed by the Picard quotient. -/
noncomputable def conductorResidueToPic (O : NumberFieldOrder K) :
    (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ × (O.conductorModulus.infinitePart → ℤˣ) →* Pic O :=
  O.rayClassToPic.comp (residueSignRayClass O.conductorModulus)

/-- The kernel of extension to the maximal order is the image of conductor residues. -/
theorem range_conductorResidueToPic (O : NumberFieldOrder K) :
    (conductorResidueToPic O).range = (orderPicToClassGroup O).ker := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, conductorResidueToPic, MonoidHom.comp_apply,
      orderPicToClassGroup_rayClassToPic, ← MonoidHom.mem_ker, ← range_residueSignRayClass]
    exact ⟨b, rfl⟩
  · intro ha
    obtain ⟨c, rfl⟩ := O.rayClassToPic_surjective a
    rw [MonoidHom.mem_ker, orderPicToClassGroup_rayClassToPic,
      ← MonoidHom.mem_ker, ← range_residueSignRayClass] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨b, rfl⟩

/-- The size identity from the actual conductor residue and class-group maps. -/
theorem card_pic_mul_conductorResidueKernel (O : NumberFieldOrder K) :
    Nat.card (Pic O) * Nat.card (conductorResidueToPic O).ker =
      Nat.card (ClassGroup (𝓞 K)) *
        Nat.card ((𝓞 K ⧸ O.conductorModulus.finitePart)ˣ ×
          (O.conductorModulus.infinitePart → ℤˣ)) := by
  rw [← Subgroup.card_ker_mul_card_range (conductorResidueToPic O), range_conductorResidueToPic,
    ← Subgroup.card_ker_mul_card_of_surjective (orderPicToClassGroup_surjective O)]
  ring

end HDec.CMBranch.FowlerArithmetic
