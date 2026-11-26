import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.PairIsomorphisms
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-! # The first j-coordinate of a cyclic pair -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

variable {k : Type*} [Field k] [DecidableEq k] {N : ℕ}

/-- The first j-coordinate is the invariant of the source elliptic curve of the pair. -/
noncomputable def pairJ : PairClasses k N → k :=
  Quot.lift (fun A : EnhancedCurve k N => letI := A.elliptic; A.equation.j) (by
    intro A B h
    let := A.elliptic
    let := B.elliptic
    obtain ⟨v, hv, _⟩ := h
    have hj := congrArg (fun W : WeierstrassCurve k => W.Δ⁻¹ * W.c₄ ^ 3) hv
    simp only [← WeierstrassCurve.j_eq] at hj
    exact (WeierstrassCurve.variableChange_j A.equation v).symm.trans hj)

@[simp] theorem pairJ_mk (A : EnhancedCurve k N) :
    pairJ (Quot.mk _ A : PairClasses k N) = (letI := A.elliptic; A.equation.j) :=
  rfl

/-- Subgroups on the given equation give classes in the fibre of its actual j-invariant. -/
noncomputable def subgroupPair (E : WeierstrassCurve k) [E.IsElliptic]
    (C : CyclicSubgroups E.toAffine.Point N) :
    {x : PairClasses k N // pairJ x = E.j} :=
  ⟨Quot.mk _ ⟨E, inferInstance, C⟩, rfl⟩

/-- Every class with the specified source invariant has a representative on the given
elliptic equation, by the equal-j isomorphism criterion over an algebraically closed field. -/
theorem subgroupPair_surjective [IsAlgClosed k] (E : WeierstrassCurve k) [E.IsElliptic] :
    Function.Surjective (subgroupPair (N := N) E) := by
  intro x
  obtain ⟨A, hA⟩ := Quot.exists_rep x.val
  let := A.elliptic
  have hj : A.equation.j = E.j := by
    rw [← x.property, ← hA, pairJ_mk]
  obtain ⟨v, hv⟩ := WeierstrassCurve.exists_variableChange_of_j_eq A.equation E hj
  let e := changePoints A.equation E v hv
  let C := cyclicSubgroupsEquiv e N A.subgroup
  refine ⟨C, Subtype.ext (?_ : (Quot.mk _ ⟨E, inferInstance, C⟩ : PairClasses k N) = x.val)⟩
  rw [← hA]
  exact ((pairClasses_eq_iff A ⟨E, inferInstance, C⟩).2 ⟨v, hv, rfl⟩).symm

#print axioms pairJ
#print axioms pairJ_mk
#print axioms subgroupPair
#print axioms subgroupPair_surjective

end WeierstrassCurve.ModelLevels.ModelGeneric2
