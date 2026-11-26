import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom

/-! # Pointwise prime-to-residue-characteristic specialization -/

namespace WeierstrassCurve.ModelLevels

open IsLocalRing
open P2MW.S_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
open P2MW.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom

/-- The cyclic subgroups of order `n` of an additive group. -/
def CyclicSubgroups (G : Type*) [AddCommGroup G] (n : ℕ) :=
  {C : AddSubgroup G // IsAddCyclic C ∧ Nat.card C = n}

/-- An additive equivalence transports cyclic subgroups with their order. -/
noncomputable def cyclicSubgroupsEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : ℕ) : CyclicSubgroups G n ≃ CyclicSubgroups H n := by
  have h (C : AddSubgroup G) :
      (IsAddCyclic (e.mapAddSubgroup C) ∧ Nat.card (e.mapAddSubgroup C) = n) ↔
        (IsAddCyclic C ∧ Nat.card C = n) := by
    rw [AddSubgroup.card_mapAddSubgroup]
    exact and_congr (e.addSubgroupMap C).isAddCyclic.symm Iff.rfl
  exact e.mapAddSubgroup.toEquiv.subtypeEquiv (fun C => (h C).symm)

variable {L : Type*} [Field L] [DecidableEq L]
variable (A : ValuationSubring L) [DecidableEq (ResidueField A)] (W : WeierstrassCurve A)
variable (hΔ : (W.map (residue A)).Δ ≠ 0)

/-- Over an algebraically closed characteristic-zero valued field with good
reduction, reduction on prime-to-residue-characteristic torsion is an additive
equivalence. This is the geometric torsion input for the kernel-indexed
operators at tex 8479–8489. -/
noncomputable def reduceTorsionEquiv [IsAlgClosed L] [CharZero L] {n : ℕ}
    (hn : (n : ResidueField A) ≠ 0) :
    AddSubgroup.torsionBy (W.map A.subtype).toAffine.Point (n : ℤ) ≃+
      AddSubgroup.torsionBy (W.map (residue A)).toAffine.Point (n : ℤ) := by
  let f : AddSubgroup.torsionBy (W.map A.subtype).toAffine.Point (n : ℤ) →+
      AddSubgroup.torsionBy (W.map (residue A)).toAffine.Point (n : ℤ) :=
    { toFun := fun x => ⟨reduceHom hΔ x.1, AddSubgroup.torsionBy.nsmul_iff.mpr <| by
        rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp x.2, map_zero]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1) }
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y he
    apply Subtype.ext
    exact ChildL.reduceHom_injOn' hΔ hn (AddSubgroup.torsionBy.nsmul_iff.mp x.2)
      (AddSubgroup.torsionBy.nsmul_iff.mp y.2) (congrArg Subtype.val he)
  · intro y
    obtain ⟨x, hx, hred⟩ := ChildL.main hΔ hn y.1 (AddSubgroup.torsionBy.nsmul_iff.mp y.2)
    exact ⟨⟨x, AddSubgroup.torsionBy.nsmul_iff.mpr hx⟩, Subtype.ext hred⟩

/-- Reduction pairs the actual cyclic kernels indexing the good Hecke
neighbors at every prime different from the residue characteristic. The
kernel order `p` is invertible in the residue field, with no condition on
`p - 1`. Quotient curves and transported level structures are additional data. -/
noncomputable def reduceCyclicKernels [IsAlgClosed L] [CharZero L] {p : ℕ}
    (hp : (p : ResidueField A) ≠ 0) :
    CyclicSubgroups (AddSubgroup.torsionBy (W.map A.subtype).toAffine.Point (p : ℤ)) p ≃
      CyclicSubgroups (AddSubgroup.torsionBy (W.map (residue A)).toAffine.Point (p : ℤ)) p :=
  cyclicSubgroupsEquiv (reduceTorsionEquiv A W hΔ hp) p

/-- Reduction of the generator's order over any valued field with good
reduction. This also applies to a generator of the kernel of a pointwise
Atkin–Lehner isogeny at an exact divisor of the level. -/
theorem reduceGenerator_order {n : ℕ} (hn : (n : ResidueField A) ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : addOrderOf P = n) :
    addOrderOf (reduceHom hΔ P) = n :=
  VeluIntegralModel.addOrderOf_reduceHom hΔ hn hP

/-- The vendored odd-order Vélu coefficient formulas interpolate the generic
and reduced quotient equations. For odd `n`, the full odd-order summing set
uses `n / 2` multiples of the generator. -/
theorem oddVelu_equations_reduce {n : ℕ} (hn : Odd n) (hunit : (n : ResidueField A) ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) (hP : addOrderOf P = n) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype =
        (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet P (n / 2)) ∧
      V.map (residue A) = (W.map (residue A)).veluQuotient
        ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ P) (n / 2)) :=
  solution A W hΔ hunit P hP (Nat.div_lt_self (by obtain ⟨m, hm⟩ := hn; omega) (by decide))

#print axioms cyclicSubgroupsEquiv
#print axioms reduceTorsionEquiv
#print axioms reduceCyclicKernels
#print axioms reduceGenerator_order
#print axioms oddVelu_equations_reduce

end WeierstrassCurve.ModelLevels
