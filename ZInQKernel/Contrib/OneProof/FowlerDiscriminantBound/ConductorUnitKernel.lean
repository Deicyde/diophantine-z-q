module

public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorResidueUnits
import all ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorResidueUnits
import all ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorUnitIndex
import all ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorClassGroup
import all ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.AwayConductor.Basic
import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.Quotient.Coprime

/-! The kernel of the conductor residue map to the Picard group of an order. -/

public section

open NumberField TauCeti.GlobalNumberFields IsDedekindDomain
open scoped nonZeroDivisors

namespace HDec.CMBranch.FowlerArithmetic

variable {K : Type*} [Field K] [NumberField K]

private noncomputable def conductorUnitsToRayClass (O : NumberFieldOrder K) :
    (𝓞 K ⧸ O.conductor)ˣ →* RayClassGroup O.conductorModulus :=
  (residueSignRayClass O.conductorModulus).comp (conductorResidueMulEquiv O).symm.toMonoidHom

private theorem conductorResidueMulEquiv_fst (O : NumberFieldOrder K)
    (r : (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ × (O.conductorModulus.infinitePart → ℤˣ)) :
    conductorResidueMulEquiv O r = r.1 := by
  rfl

private theorem conductorResidue_of_integral (O : NumberFieldOrder K)
    (x : primeToSubgroup O.conductorModulus) {β : 𝓞 K}
    (hx : ((x : Kˣ) : K) = β) :
    (conductorResidueMulEquiv O (residueSignHom O.conductorModulus x) : 𝓞 K ⧸ O.conductor) =
      Ideal.Quotient.mk O.conductor β := by
  rw [conductorResidueMulEquiv_fst, residueSignHom_fst, coe_residueHom]
  exact residue_eq x (b := 1) (by simp) (by simpa using hx.symm)

private theorem conductorUnitsToRayClass_of_generator (O : NumberFieldOrder K)
    (J : integralIdealsPrimeTo O.conductorModulus) {β : 𝓞 K}
    (hJ : (J : Ideal (𝓞 K)) = Ideal.span {β}) {u : (𝓞 K ⧸ O.conductor)ˣ}
    (hu : Ideal.Quotient.mk O.conductor β = ↑u) :
    conductorUnitsToRayClass O u = idealClass O.conductorModulus J := by
  have hβ : β ≠ 0 := by
    intro h
    exact (O.mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.2).1
      (hJ.trans (Ideal.span_singleton_eq_bot.mpr h))
  let y : Kˣ := Units.mk0 (β : K) (by simpa using hβ)
  have hy : (y : K) = β := rfl
  let x : primeToSubgroup O.conductorModulus := ⟨y, mem_primeToSubgroup.mpr (by
    intro v hv
    rw [hy, HeightOneSpectrum.valuation_of_algebraMap]
    apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
    intro hm
    have hJ' := Modulus.isCoprimeTo_iff.mp (Modulus.mem_integralIdealsPrimeTo.mp J.2)
    apply hJ'.2 v ((Modulus.mem_support_iff _ _).mpr hv)
    rw [hJ]
    exact Ideal.dvd_span_singleton.mpr hm)⟩
  have hx : ((x : Kˣ) : K) = β := hy
  have hu' : conductorResidueMulEquiv O (residueSignHom O.conductorModulus x) = u :=
    Units.ext ((conductorResidue_of_integral O x hx).trans hu)
  have hr : (conductorResidueMulEquiv O).symm u = residueSignHom O.conductorModulus x :=
    (MulEquiv.symm_apply_eq _).mpr hu'.symm
  rw [conductorUnitsToRayClass, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hr,
    residueSignRayClass_residueSignHom, principalRayClass_apply, idealClass_apply]
  refine congrArg (rayClassMk _) (Subtype.ext (Units.ext ?_))
  rw [TauCeti.NumberFieldArithmetic.coe_principalIdealAway, coe_toPrincipalIdeal,
    TauCeti.NumberFieldArithmetic.coe_integralIdealsAwayHom, hJ,
    FractionalIdeal.coeIdeal_span_singleton, hx]

private theorem ker_conductorUnitsToRayClass (O : NumberFieldOrder K) :
    (conductorUnitsToRayClass O).ker = (maximalUnitsModConductor O).range := by
  have hunit (v : (𝓞 K)ˣ) :
      conductorResidueMulEquiv O (unitsResidueSignHom O.conductorModulus v) =
        maximalUnitsModConductor O v := by
    have hv : (((unitsToPrimeToSubgroup O.conductorModulus v) : Kˣ) : K) = (v : 𝓞 K) := by
      rw [coe_unitsToPrimeToSubgroup]
      rfl
    apply Units.ext
    rw [unitsResidueSignHom_apply, conductorResidue_of_integral O _ hv]
    rfl
  ext u
  change (conductorResidueMulEquiv O).symm u ∈ (residueSignRayClass O.conductorModulus).ker ↔ _
  rw [ker_residueSignRayClass]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (hunit v).symm.trans ((congrArg (conductorResidueMulEquiv O) hv).trans
      ((conductorResidueMulEquiv O).apply_symm_apply u))⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, (MulEquiv.eq_symm_apply _).mpr (hunit v)⟩

private theorem map_orderResidueUnitSubgroup (O : NumberFieldOrder K) :
    (orderResidueUnitSubgroup O).map (conductorUnitsToRayClass O) = O.rayClassToPic.ker := by
  have hfinite : Finite (𝓞 K ⧸ O.conductor) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ O.conductor_ne_bot
  apply le_antisymm
  · rintro _ ⟨u, ⟨v, rfl⟩, rfl⟩
    let u := Units.map (orderResidueToMaximal O).toMonoidHom v
    obtain ⟨a, ha⟩ : ∃ a : O.toRingOfIntegers, Ideal.Quotient.mk _ a =
        (v : O.toRingOfIntegers ⧸ orderConductorIdeal O) := Ideal.Quotient.mk_surjective _
    have hu : Ideal.Quotient.mk O.conductor (a : 𝓞 K) = ↑u :=
      congrArg (orderResidueToMaximal O) ha
    by_cases htop : O.conductor = ⊤
    · let : Subsingleton (𝓞 K ⧸ O.conductor) := Ideal.Quotient.subsingleton_iff.mpr htop
      have h : u = 1 := Units.ext (Subsingleton.elim _ _)
      change conductorUnitsToRayClass O u ∈ _
      rw [h, map_one]
      exact O.rayClassToPic.ker.one_mem
    have hcop : Ideal.span {(a : 𝓞 K)} ⊔ O.conductor = ⊤ := by
      apply Ideal.Quotient.isUnit_mk_iff.mp
      rw [hu]
      exact u.isUnit
    have hne : Ideal.span {(a : 𝓞 K)} ≠ ⊥ := by
      intro h
      exact htop (by simpa [h] using hcop)
    let J : integralIdealsPrimeTo O.conductorModulus :=
      ⟨_, O.mem_integralIdealsPrimeTo_conductorModulus_iff.mpr ⟨hne, hcop⟩⟩
    exact O.mem_ker_rayClassToPic.mpr
      ⟨J, (conductorUnitsToRayClass_of_generator O J rfl hu).symm, a, a.property, rfl⟩
  · intro c hc
    obtain ⟨J, hClass, β, hβ, hJ⟩ := O.mem_ker_rayClassToPic.mp hc
    let a : O.toRingOfIntegers := ⟨β, hβ⟩
    have hcop : Ideal.span {β} ⊔ O.conductor = ⊤ :=
      hJ ▸ (O.mem_integralIdealsPrimeTo_conductorModulus_iff.mp J.2).2
    have hcop' : Ideal.span {a} ⊔ orderConductorIdeal O = ⊤ :=
      Ideal.span_singleton_sup_comap_eq_top (C := O.conductor) (x := a)
        (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) hcop
    have hv : IsUnit (Ideal.Quotient.mk (orderConductorIdeal O) a) :=
      Ideal.Quotient.isUnit_mk_iff.mpr hcop'
    let u := Units.map (orderResidueToMaximal O).toMonoidHom hv.unit
    have hu : Ideal.Quotient.mk O.conductor β = ↑u :=
      (congrArg (orderResidueToMaximal O) hv.unit_spec).symm
    exact ⟨u, ⟨hv.unit, rfl⟩, (conductorUnitsToRayClass_of_generator O J hJ hu).trans hClass⟩

/-- The residue classes killed in `Pic O` are the products of reduced maximal-order units
and the images of units in the order modulo its conductor. -/
theorem ker_conductorUnitsToPic (O : NumberFieldOrder K) :
    (conductorUnitsToPic O).ker =
      (maximalUnitsModConductor O).range ⊔ orderResidueUnitSubgroup O := by
  have h : (conductorUnitsToPic O).ker = O.rayClassToPic.ker.comap
      (conductorUnitsToRayClass O) := rfl
  rw [h, ← map_orderResidueUnitSubgroup, Subgroup.comap_map_eq, ker_conductorUnitsToRayClass,
    sup_comm]

end HDec.CMBranch.FowlerArithmetic
