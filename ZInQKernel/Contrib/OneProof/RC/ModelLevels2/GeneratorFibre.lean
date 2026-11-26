import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.FibrePoints
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.GeneratorOrbits

/-! # Generator orbits in the fibres of the relative cover -/

namespace WeierstrassCurve.ModelLevels

variable {A k : Type*} [CommRing A] [Field k] [Algebra A k] [DecidableEq k]
  (W : WeierstrassCurve A) [W.IsElliptic] {N : ℕ} (hN : IsUnit (N : A))

/-- The geometric unit action on field-valued points of the exact-order
cover, obtained by reading a point of the specialized curve and multiplying
it. This is an action on field-valued points. -/
@[instance_reducible] noncomputable def generatorFibreAction [NeZero N] :
    MulAction (ZMod N)ˣ (ExactOrderAlgebra W hN →ₐ[A] k) := by
  let e : (ExactOrderAlgebra W hN →ₐ[A] k) ≃
      Generators (W.map (algebraMap A k)).toAffine.Point N := exactOrderFibrePoints W hN
  exact {
    smul := fun a x => e.symm (a • e x)
    one_smul := fun x => (congrArg e.symm (one_smul _ (e x))).trans (e.symm_apply_apply x)
    mul_smul := by
      intro a b x
      change e.symm ((a * b) • e x) = e.symm (a • e (e.symm (b • e x)))
      rw [e.apply_symm_apply, mul_smul] }

/-- The generator represented by a translated cover point is the
natural-number representative of the unit times the original generator. -/
theorem generatorFibreAction_point [NeZero N] (a : (ZMod N)ˣ)
    (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    (exactOrderFibrePoints W hN ((generatorFibreAction W hN).smul a f)).1 =
      (a : ZMod N).val • (exactOrderFibrePoints W hN f).1 := by
  let e : (ExactOrderAlgebra W hN →ₐ[A] k) ≃
      Generators (W.map (algebraMap A k)).toAffine.Point N := exactOrderFibrePoints W hN
  change (e (e.symm (a • e f))).1 = (a : ZMod N).val • (e f).1
  rw [e.apply_symm_apply]
  exact generatorAction_apply _ _

/-- In each field fibre the generator orbits are exactly the actual cyclic
subgroups. The construction applies over the algebraic closure of the
detector's residue field whenever the level is invertible there. -/
noncomputable def generatorFibreOrbitEquiv [NeZero N] :
    @Quotient _ (@MulAction.orbitRel (ZMod N)ˣ (ExactOrderAlgebra W hN →ₐ[A] k) _
      (generatorFibreAction (k := k) W hN)) ≃
      CyclicSubgroups (W.map (algebraMap A k)).toAffine.Point N := by
  letI := generatorFibreAction (k := k) W hN
  let e : (ExactOrderAlgebra W hN →ₐ[A] k) ≃
      Generators (W.map (algebraMap A k)).toAffine.Point N := exactOrderFibrePoints W hN
  let f : (ExactOrderAlgebra W hN →ₐ[A] k) →
      CyclicSubgroups (W.map (algebraMap A k)).toAffine.Point N :=
    fun x => subgroupOfGenerator (e x)
  have horbit (x y : ExactOrderAlgebra W hN →ₐ[A] k) :
      MulAction.orbitRel (ZMod N)ˣ _ x y ↔ f x = f y := by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    change (∃ a : (ZMod N)ˣ, e.symm (a • e y) = x) ↔ _
    simp only [Equiv.symm_apply_eq]
    rw [generatorOrbit_iff]
    exact ⟨fun h => Subtype.ext h.symm,
      fun h => (congrArg Subtype.val h).symm⟩
  apply Equiv.ofBijective (Quotient.lift f fun x y h => (horbit x y).1 h)
  constructor
  · intro x y
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact fun h => Quotient.sound ((horbit _ _).2 h)
  · intro C
    obtain ⟨P, hP⟩ := subgroupOfGenerator_surjective C
    exact ⟨Quotient.mk'' (e.symm P), by
      change subgroupOfGenerator (e (e.symm P)) = C
      rw [e.apply_symm_apply, hP]⟩

#print axioms generatorFibreAction
#print axioms generatorFibreAction_point
#print axioms generatorFibreOrbitEquiv

end WeierstrassCurve.ModelLevels
