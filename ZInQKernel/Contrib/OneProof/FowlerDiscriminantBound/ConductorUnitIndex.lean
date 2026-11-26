module

public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorClassGroup

/-! The index calculation for the conductor class-number formula. -/

public section

open NumberField TauCeti.GlobalNumberFields

namespace HDec.CMBranch.FowlerArithmetic

variable {K : Type*} [Field K] [NumberField K]

/-- The residue-and-sign type specializes to the finite residue units at the conductor. -/
noncomputable def conductorResidueMulEquiv (O : NumberFieldOrder K) :
    ((𝓞 K ⧸ O.conductorModulus.finitePart)ˣ × (O.conductorModulus.infinitePart → ℤˣ)) ≃*
      (𝓞 K ⧸ O.conductor)ˣ := by
  letI : Subsingleton (O.conductorModulus.infinitePart → ℤˣ) := ⟨fun f g => funext fun a => by
    obtain ⟨x, hx⟩ := a
    exact (Finset.notMem_empty x (by simpa only [O.conductorModulus_infinitePart] using hx)).elim⟩
  let e : (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ ≃* (𝓞 K ⧸ O.conductor)ˣ := by
    rw [O.conductorModulus_finitePart]
  exact
    { toFun := fun u => e u.1
      invFun := fun u => (e.symm u, 1)
      left_inv := fun u => Prod.ext (e.symm_apply_apply u.1) (Subsingleton.elim _ _)
      right_inv := e.apply_symm_apply
      map_mul' := fun u v => e.map_mul u.1 v.1 }

/-- The actual conductor residue map, with the empty sign factor removed. -/
noncomputable def conductorUnitsToPic (O : NumberFieldOrder K) :
    (𝓞 K ⧸ O.conductor)ˣ →* Pic O :=
  (conductorResidueToPic O).comp (conductorResidueMulEquiv O).symm.toMonoidHom

/-- The reduction on actual maximal-order units. -/
@[expose] def maximalUnitsModConductor (O : NumberFieldOrder K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ O.conductor)ˣ :=
  Units.map (Ideal.Quotient.mk O.conductor).toMonoidHom

private theorem card_conductorUnitsToPic_ker (O : NumberFieldOrder K) :
    Nat.card (conductorUnitsToPic O).ker = Nat.card (conductorResidueToPic O).ker := by
  have hmap : (conductorResidueToPic O).ker.map (conductorResidueMulEquiv O).toMonoidHom =
      (conductorUnitsToPic O).ker := by
    apply Subgroup.ext
    intro u
    change (∃ b, b ∈ (conductorResidueToPic O).ker ∧ conductorResidueMulEquiv O b = u) ↔
      conductorUnitsToPic O u = 1
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa [conductorUnitsToPic, MonoidHom.mem_ker] using hb
    · intro hu
      refine ⟨(conductorResidueMulEquiv O).symm u, ?_,
        (conductorResidueMulEquiv O).apply_symm_apply u⟩
      simpa [conductorUnitsToPic, MonoidHom.mem_ker] using hu
  rw [← hmap]
  exact (Nat.card_congr ((conductorResidueToPic O).ker.equivMapOfInjective _
    (conductorResidueMulEquiv O).injective).toEquiv).symm

/-- Without the empty sign factor, the class-number identity uses exactly the conductor units. -/
theorem card_pic_mul_conductorUnitKernel (O : NumberFieldOrder K) :
    Nat.card (Pic O) * Nat.card (conductorUnitsToPic O).ker =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ O.conductor)ˣ := by
  rw [card_conductorUnitsToPic_ker, card_pic_mul_conductorResidueKernel,
    Nat.card_congr (conductorResidueMulEquiv O).toEquiv]

/-- Once the residue kernel is identified as the product of the scalar residues and the image of
maximal-order units, the remaining unit factor is the index of the preimage of the scalars. -/
theorem card_pic_mul_scalar_and_unit_index (O : NumberFieldOrder K)
    (S : Subgroup (𝓞 K ⧸ O.conductor)ˣ)
    (hker : (conductorUnitsToPic O).ker = (maximalUnitsModConductor O).range ⊔ S) :
    Nat.card (Pic O) * Nat.card S * (S.comap (maximalUnitsModConductor O)).index =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ O.conductor)ˣ := by
  have h := Subgroup.relIndex_mul_card S ((maximalUnitsModConductor O).range ⊔ S)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right, ← Subgroup.index_comap] at h
  rw [mul_assoc, mul_comm (Nat.card S), h, ← hker, card_pic_mul_conductorUnitKernel]

end HDec.CMBranch.FowlerArithmetic
