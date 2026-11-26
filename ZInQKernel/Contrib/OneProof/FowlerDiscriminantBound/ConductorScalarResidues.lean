module

public import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorResidueUnits
import all ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorResidueUnits
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor
public import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.Unimodular

/-! # Scalar residues of quadratic orders

The quotient of the actual order by its conductor is `ZMod O.index`. Its units identify
with the subgroup of maximal-order residue units coming from the order.
-/

public section

open NumberField TauCeti.GlobalNumberFields

namespace HDec.CMBranch.FowlerArithmetic

variable {K : Type*} [Field K] [NumberField K]

private theorem intCast_mem_conductor_iff (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (a : ℤ) :
    (a : 𝓞 K) ∈ O.conductor ↔ (O.index : ℤ) ∣ a := by
  rw [O.conductor_eq_span_index hK, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨b, hb⟩ := (Module.Free.isUnimodular_one (R := ℤ) (A := 𝓞 K)).exists_basis_zero_eq
      (by rw [RingOfIntegers.rank, hK])
    have hscalar : (a : 𝓞 K) = a • b 0 := by simp [hb, Algebra.smul_def]
    have hmul : (a : 𝓞 K) = (O.index : ℤ) • y := by
      simpa [Algebra.smul_def] using hy
    refine ⟨b.coord 0 y, ?_⟩
    have hcoord := congrArg (b.coord 0) hmul
    rw [hscalar, map_smul, map_smul] at hcoord
    simpa [Module.Basis.coord_apply] using hcoord
  · rintro ⟨a, rfl⟩
    exact ⟨(a : 𝓞 K), by simp⟩

private theorem intCast_orderResidue_eq_zero_iff (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (a : ℤ) :
    (a : O.toRingOfIntegers ⧸ orderConductorIdeal O) = 0 ↔ (O.index : ℤ) ∣ a := by
  rw [← map_intCast (Ideal.Quotient.mk (orderConductorIdeal O)), Ideal.Quotient.eq_zero_iff_mem]
  change (a : 𝓞 K) ∈ O.conductor ↔ _
  exact intCast_mem_conductor_iff O hK a

/-- The canonical inclusion of the order residue ring has trivial kernel. -/
theorem orderResidueToMaximal_injective (O : NumberFieldOrder K) :
    Function.Injective (orderResidueToMaximal O) := by
  unfold orderResidueToMaximal
  exact Ideal.quotientMap_injective

/-- The integer cast realizes `ZMod O.index` as the actual order modulo the conductor. -/
noncomputable def zmodEquivOrderResidue (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) :
    ZMod O.index ≃+* O.toRingOfIntegers ⧸ orderConductorIdeal O := by
  letI : CharP (O.toRingOfIntegers ⧸ orderConductorIdeal O) O.index := ⟨fun a ↦ by
    rw [← Int.cast_natCast, intCast_orderResidue_eq_zero_iff O hK, Int.natCast_dvd_natCast]⟩
  refine RingEquiv.ofBijective (ZMod.castHom (dvd_refl O.index) _) ⟨ZMod.castHom_injective _, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, y, hxy⟩ :=
    (O.mem_toRingOfIntegers_iff_exists_int_add_index_mul hK (x : 𝓞 K)).mp x.property
  refine ⟨(a : ZMod O.index), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (orderConductorIdeal O))]
  apply Ideal.Quotient.eq.mpr
  change (a : 𝓞 K) - (x : 𝓞 K) ∈ O.conductor
  rw [hxy, sub_add_eq_sub_sub, sub_self, zero_sub]
  exact O.conductor.neg_mem (O.conductor.mul_mem_right y O.natCast_index_mem_conductor)

/-- Integer representatives reduce to the same integers in the maximal quotient. -/
theorem orderResidueToMaximal_zmodEquivOrderResidue_intCast (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (a : ℤ) :
    orderResidueToMaximal O (zmodEquivOrderResidue O hK (a : ZMod O.index)) =
      (a : 𝓞 K ⧸ O.conductor) := by
  rw [map_intCast, map_intCast]

/-- Reduction of scalar units identifies them with the actual order-residue unit subgroup. -/
noncomputable def zmodUnitsEquivOrderResidueUnitSubgroup (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) : (ZMod O.index)ˣ ≃* orderResidueUnitSubgroup O := by
  unfold orderResidueUnitSubgroup
  exact (Units.mapEquiv (zmodEquivOrderResidue O hK).toMulEquiv).trans
    (MonoidHom.ofInjective (Units.map_injective (orderResidueToMaximal_injective O)))

/-- The scalar residue factor in the conductor formula is Euler's totient of the index. -/
theorem card_orderResidueUnitSubgroup_eq_totient (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) :
    Nat.card (orderResidueUnitSubgroup O) = Nat.totient O.index := by
  rw [Nat.card_congr (zmodUnitsEquivOrderResidueUnitSubgroup O hK).symm.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- At index one, the maximal-order residue ring is the zero ring and the subgroup is trivial. -/
theorem orderResidueUnitSubgroup_eq_bot_of_index_eq_one (O : NumberFieldOrder K)
    (h : O.index = 1) : orderResidueUnitSubgroup O = ⊥ := by
  have htop : O.conductor = ⊤ :=
    (O.conductor_eq_top_iff).mpr ((O.index_eq_one_iff).mp h)
  let _ : Subsingleton (𝓞 K ⧸ O.conductor) := Ideal.Quotient.subsingleton_iff.mpr htop
  exact le_antisymm (fun x _ ↦ Subgroup.mem_bot.mpr (Units.ext (Subsingleton.elim _ _))) bot_le

end HDec.CMBranch.FowlerArithmetic
