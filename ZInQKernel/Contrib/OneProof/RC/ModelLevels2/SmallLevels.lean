import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.FibrePoints
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.GeneratorOrbits

/-! # The trivial unit action at levels one and two -/

namespace WeierstrassCurve.ModelLevels

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]
  {N : ℕ} (hN : IsUnit (N : A))

private theorem smallLevel_unit_eq_one (hle : N = 1 ∨ N = 2) (a : (ZMod N)ˣ) : a = 1 := by
  obtain rfl | rfl := hle
  · exact Subsingleton.elim _ _
  · exact (Fintype.card_le_one_iff_subsingleton.mp (by rw [ZMod.card_units_eq_totient]; decide)).elim _ _

/-- The algebra action at levels one and two is the identity.
The level-one algebra is the coefficient ring, representing the identity
point. -/
noncomputable def smallLevelUnitAut (_hle : N = 1 ∨ N = 2) :
    (ZMod N)ˣ →* (ExactOrderAlgebra W hN ≃ₐ[A] ExactOrderAlgebra W hN) :=
  1

/-- The identity action at levels one and two induces the geometric unit
action on the exact-order points. -/
theorem smallLevelUnitAut_point [NeZero N] {k : Type*} [Field k] [Algebra A k] [DecidableEq k]
    (hle : N = 1 ∨ N = 2) (a : (ZMod N)ˣ) (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    (exactOrderFibrePoints W hN (f.comp ((smallLevelUnitAut W hN hle) a).toAlgHom) :
      Generators (W.map (algebraMap A k)).toAffine.Point N) =
        (generatorAction (G := (W.map (algebraMap A k)).toAffine.Point) (N := N)).smul a
          (exactOrderFibrePoints W hN f) := by
  let P : Generators (W.map (algebraMap A k)).toAffine.Point N := exactOrderFibrePoints W hN f
  change P = a • P
  rw [smallLevel_unit_eq_one hle a, one_smul]

#print axioms smallLevel_unit_eq_one
#print axioms smallLevelUnitAut
#print axioms smallLevelUnitAut_point

end WeierstrassCurve.ModelLevels
