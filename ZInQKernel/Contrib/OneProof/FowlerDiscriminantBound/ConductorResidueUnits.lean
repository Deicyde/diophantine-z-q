module

public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorUnitIndex
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The order-unit subgroup is the inverse image of its units modulo the conductor. -/

public section

open NumberField TauCeti.GlobalNumberFields

namespace HDec.CMBranch.FowlerArithmetic

variable {K : Type*} [Field K] [NumberField K]

/-- The conductor on the order, viewed inside its copy in the ring of integers. -/
abbrev orderConductorIdeal (O : NumberFieldOrder K) : Ideal O.toRingOfIntegers :=
  O.conductor.comap O.toRingOfIntegers.val

/-- The canonical inclusion of the order residue ring into the maximal-order residue ring. -/
def orderResidueToMaximal (O : NumberFieldOrder K) :
    O.toRingOfIntegers ⧸ orderConductorIdeal O →+* 𝓞 K ⧸ O.conductor :=
  Ideal.quotientMap O.conductor O.toRingOfIntegers.val le_rfl

/-- The actual subgroup of residue units coming from the order. -/
def orderResidueUnitSubgroup (O : NumberFieldOrder K) : Subgroup (𝓞 K ⧸ O.conductor)ˣ :=
  (Units.map (orderResidueToMaximal O).toMonoidHom).range

private theorem mem_order_of_residue_mem_range (O : NumberFieldOrder K) {x : 𝓞 K}
    {y : O.toRingOfIntegers ⧸ orderConductorIdeal O}
    (h : orderResidueToMaximal O y = Ideal.Quotient.mk O.conductor x) :
    x ∈ O.toRingOfIntegers := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.mk O.conductor (a : 𝓞 K) = Ideal.Quotient.mk O.conductor x at h
  have hd : x - (a : 𝓞 K) ∈ O.conductor := Ideal.Quotient.eq.mp h.symm
  have hm : x - (a : 𝓞 K) ∈ O.toRingOfIntegers := O.conductor_le_toRingOfIntegers hd
  simpa using O.toRingOfIntegers.add_mem hm a.property

/-- An integer unit has order residue precisely if it comes from an actual unit of the order.
The inverse residue supplies the inverse in the order; no field-specific unit classification
is needed for this preimage identity. -/
theorem comap_orderResidueUnitSubgroup (O : NumberFieldOrder K) :
    (orderResidueUnitSubgroup O).comap (maximalUnitsModConductor O) =
      (Units.map O.toRingOfIntegers.val.toMonoidHom).range := by
  apply Subgroup.ext
  intro u
  change (∃ v : (O.toRingOfIntegers ⧸ orderConductorIdeal O)ˣ,
    Units.map (orderResidueToMaximal O).toMonoidHom v = maximalUnitsModConductor O u) ↔
    ∃ z : (O.toRingOfIntegers)ˣ, Units.map O.toRingOfIntegers.val.toMonoidHom z = u
  constructor
  · rintro ⟨v, hv⟩
    have hval : orderResidueToMaximal O (v : O.toRingOfIntegers ⧸ orderConductorIdeal O) =
        Ideal.Quotient.mk O.conductor (u : 𝓞 K) := congrArg Units.val hv
    have hv_inv : Units.map (orderResidueToMaximal O).toMonoidHom v⁻¹ =
        maximalUnitsModConductor O u⁻¹ := by rw [map_inv, hv, map_inv]
    have hinv : orderResidueToMaximal O
        (↑(v⁻¹) : O.toRingOfIntegers ⧸ orderConductorIdeal O) =
        Ideal.Quotient.mk O.conductor (↑(u⁻¹) : 𝓞 K) := congrArg Units.val hv_inv
    let z : (O.toRingOfIntegers)ˣ :=
      { val := ⟨_, mem_order_of_residue_mem_range O hval⟩
        inv := ⟨_, mem_order_of_residue_mem_range O hinv⟩
        val_inv := Subtype.ext u.val_inv
        inv_val := Subtype.ext u.inv_val }
    exact ⟨z, Units.ext rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨Units.map (Ideal.Quotient.mk (orderConductorIdeal O)).toMonoidHom z, Units.ext ?_⟩
    change orderResidueToMaximal O (Ideal.Quotient.mk _ (z : O.toRingOfIntegers)) =
      Ideal.Quotient.mk O.conductor ((z : O.toRingOfIntegers) : 𝓞 K)
    rfl

/-- The global class-number formula reduces to the actual subgroup identity at the conductor.
The unit index is the index of the natural map from order units to integer units. -/
theorem card_pic_mul_orderResidueUnits_and_unit_index (O : NumberFieldOrder K)
    (hker : (conductorUnitsToPic O).ker =
      (maximalUnitsModConductor O).range ⊔ orderResidueUnitSubgroup O) :
    Nat.card (Pic O) * Nat.card (orderResidueUnitSubgroup O) *
        (Units.map O.toRingOfIntegers.val.toMonoidHom).range.index =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ O.conductor)ˣ := by
  have h := card_pic_mul_scalar_and_unit_index O (orderResidueUnitSubgroup O) hker
  rwa [comap_orderResidueUnitSubgroup] at h

end HDec.CMBranch.FowlerArithmetic
