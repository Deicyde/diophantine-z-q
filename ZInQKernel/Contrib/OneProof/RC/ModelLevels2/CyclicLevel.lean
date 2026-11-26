import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.GeneratorFibre
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.SmallLevels
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.UnitAction
import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.FinitePoints
import Mathlib.RingTheory.Smooth.Flat

/-! # The cyclic-subgroup quotient over the coefficient chart -/

namespace WeierstrassCurve.ModelLevels

open RC.ModelInvariants
open scoped TensorProduct

variable {A : Type*} [CommRing A] [IsDomain A]
  (W : WeierstrassCurve A) [W.IsElliptic] {N : ℕ} (hN : IsUnit (N : A)) (h₂ : 2 ≤ N)

/-- Geometric unit multiplication on the exact-order algebra at every
level at least two. -/
noncomputable def levelUnitAut :
    (ZMod N)ˣ →* (ExactOrderAlgebra W hN ≃ₐ[A] ExactOrderAlgebra W hN) := by
  obtain _ | _ | _ | n := N
  · omega
  · omega
  · exact smallLevelUnitAut W hN (Or.inr rfl)
  · exact exactOrderUnitAut W hN

/-- The pinned algebra action induces multiplication on each point of the
cover over a field-valued coefficient point. -/
theorem levelUnitAut_point {k : Type*} [Field k] [Algebra A k] [DecidableEq k]
    (a : (ZMod N)ˣ) (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    (exactOrderFibrePoints W hN (f.comp ((levelUnitAut W hN h₂) a).toAlgHom)).1 =
      (a : ZMod N).val • (exactOrderFibrePoints W hN f).1 := by
  obtain _ | _ | _ | n := N
  · omega
  · omega
  · exact congrArg Subtype.val (smallLevelUnitAut_point W hN (Or.inr rfl) a f)
  · exact exactOrderUnitAut_point W hN a f

/-- The action as semiring automorphisms, with the geometric definitions
of multiplication by a unit fixed. -/
@[instance_reducible] noncomputable def levelSemiringAction :
    MulSemiringAction (ZMod N)ˣ (ExactOrderAlgebra W hN) :=
  MulSemiringAction.compHom (ExactOrderAlgebra W hN) (levelUnitAut W hN h₂)

private theorem level_smulCommClass :
    letI := levelSemiringAction W hN h₂
    SMulCommClass (ZMod N)ˣ A (ExactOrderAlgebra W hN) := by
  letI := levelSemiringAction W hN h₂
  refine ⟨fun a r x => ?_⟩
  exact ((levelUnitAut W hN h₂) a).toAlgHom.toLinearMap.map_smul r x

/-- The finite-group quotient of the exact-order cover over the
coefficient chart. Its operators are fixed by geometric unit multiplication. -/
noncomputable abbrev CyclicLevelAlgebra : Subalgebra A (ExactOrderAlgebra W hN) :=
  letI := levelSemiringAction W hN h₂
  letI := level_smulCommClass W hN h₂
  FixedPoints.subalgebra A (ExactOrderAlgebra W hN) (ZMod N)ˣ

/-- In a fixed coefficient fibre, points of the finite-group quotient
give cyclic subgroups on the specialized short curve. This includes an
algebraic closure of the detector residue field when the level and the
unit-group order are invertible. -/
noncomputable def cyclicLevelPoints {k : Type*} [Field k] [Algebra A k] [DecidableEq k]
    [IsAlgClosed k] [NeZero N] [Fintype (ZMod N)ˣ]
    (hφ : IsUnit (Fintype.card ((ZMod N)ˣ) : A)) :
    (CyclicLevelAlgebra W hN h₂ →ₐ[A] k) ≃
      CyclicSubgroups (W.map (algebraMap A k)).toAffine.Point N := by
  letI := levelSemiringAction W hN h₂
  letI := level_smulCommClass W hN h₂
  let e := (fixedPointsOrbitEquiv (R := A) (S := ExactOrderAlgebra W hN)
    (G := (ZMod N)ˣ) (k := k) hφ).symm
  refine e.trans ((Quotient.congrRight ?_).trans (generatorFibreOrbitEquiv W hN))
  intro f g
  change (∃ a : (ZMod N)ˣ, a • g = f) ↔
    (∃ a : (ZMod N)ˣ, (generatorFibreAction W hN).smul a g = f)
  have ha (a : (ZMod N)ˣ) : a • g = (generatorFibreAction W hN).smul a⁻¹ g := by
    apply (exactOrderFibrePoints W hN).injective
    apply Subtype.ext
    exact (levelUnitAut_point W hN h₂ a⁻¹ g).trans (generatorFibreAction_point W hN a⁻¹ g).symm
  constructor
  · rintro ⟨a, h⟩
    exact ⟨a⁻¹, (ha a).symm.trans h⟩
  · rintro ⟨a, h⟩
    exact ⟨a⁻¹, (ha a⁻¹).trans (by simpa only [inv_inv] using h)⟩

/-- Arbitrary base change of the finite-group quotient for the pinned
action, including scalar extension to a residue field. -/
noncomputable def cyclicLevelBaseChange [Fintype (ZMod N)ˣ]
    (hφ : IsUnit (Fintype.card ((ZMod N)ˣ) : A))
    (B : Type*) [CommRing B] [Algebra A B] :
    letI := levelSemiringAction W hN h₂
    letI := level_smulCommClass W hN h₂
    B ⊗[A] CyclicLevelAlgebra W hN h₂ ≃ₐ[B]
      FixedPoints.subalgebra B (B ⊗[A] ExactOrderAlgebra W hN) (ZMod N)ˣ := by
  letI := levelSemiringAction W hN h₂
  letI := level_smulCommClass W hN h₂
  exact fixedPointsBaseChange B hφ

/-- The finite-group quotient of the cover is flat over the coefficient
chart whenever the group order is a unit. -/
theorem cyclicLevel_flat [Fintype (ZMod N)ˣ]
    (hφ : IsUnit (Fintype.card ((ZMod N)ˣ) : A)) :
    Module.Flat A (CyclicLevelAlgebra W hN h₂) := by
  letI := levelSemiringAction W hN h₂
  letI := level_smulCommClass W hN h₂
  letI : Algebra.Etale A (ExactOrderAlgebra W hN) := (exactOrderAlgebra_finite_etale W hN).2
  exact fixedPoints_flat hφ

#print axioms levelUnitAut
#print axioms levelUnitAut_point
#print axioms levelSemiringAction
#print axioms level_smulCommClass
#print axioms CyclicLevelAlgebra
#print axioms cyclicLevelPoints
#print axioms cyclicLevelBaseChange
#print axioms cyclicLevel_flat

end WeierstrassCurve.ModelLevels
