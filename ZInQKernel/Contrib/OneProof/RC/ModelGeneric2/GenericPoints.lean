import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.GenericJ
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.RationalPoints
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.ShortSubgroups

/-! # Restrict the pinned geometric reading to the generic j-point -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric
open scoped TensorProduct

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric points over the generic j-line are the rational quotient points whose
first coordinate is the image of the indeterminate. -/
noncomputable def genericJPointsOnRational :
    (Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) ≃
      {x : Y0RationalAlgebra h₂ →ₐ[ℚ] Kbar //
        x (Y0RationalJ h₂) = algebraMap Qj Kbar RatFunc.X} := by
  let P := Polynomial ℚ
  let B := Y0RationalAlgebra h₂
  letI : Algebra P B := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Algebra P Kbar := inferInstanceAs (Algebra (Polynomial ℚ) Kbar)
  letI : IsScalarTower P Qj Kbar := inferInstanceAs (IsScalarTower (Polynomial ℚ) Qj Kbar)
  letI : IsScalarTower ℚ P Kbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  letI : IsScalarTower ℚ P B := IsScalarTower.of_algebraMap_eq' (Y0RationalJMap h₂).comp_algebraMap.symm
  refine (AlgHom.liftEquiv P Qj B Kbar).symm.trans
    { toFun := fun f => ⟨f.restrictScalars ℚ, ?_⟩
      invFun := fun x => ⟨x.val.toRingHom, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · change f (Y0RationalJ h₂) = _
    have hj : algebraMap P B Polynomial.X = Y0RationalJ h₂ := Polynomial.aeval_X _
    rw [← hj, f.commutes, IsScalarTower.algebraMap_apply P Qj Kbar, RatFunc.algebraMap_X]
  · have h : x.val.comp (Y0RationalJMap h₂) = IsScalarTower.toAlgHom ℚ P Kbar := by
      apply Polynomial.algHom_ext
      change x.val ((Y0RationalJMap h₂) Polynomial.X) =
        algebraMap P Kbar Polynomial.X
      rw [show (Y0RationalJMap h₂) Polynomial.X = Y0RationalJ h₂ from Polynomial.aeval_X _,
        IsScalarTower.algebraMap_apply P Qj Kbar, RatFunc.algebraMap_X]
      exact x.property
    exact DFunLike.congr_fun h

/-- Restriction to the rational quotient is evaluation on its localization inclusion. -/
theorem genericJPointsOnRational_apply (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar)
    (b : Y0RationalAlgebra h₂) :
    (genericJPointsOnRational h₂ x).val b = x (Y0RationalGenericJInclusion h₂ b) :=
  rfl

/-- The generic j-fibre reads as the classes of cyclic pairs with the same source invariant
as the pinned generic elliptic curve. -/
noncomputable def genericJPairClasses :
    (Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) ≃
      {x : PairClasses Kbar N // pairJ x = algebraMap Qj Kbar RatFunc.X} :=
  (genericJPointsOnRational h₂).trans <|
    (rationalPoints h₂).subtypeEquiv fun x => by
      rw [rationalPoints_j]

private noncomputable def genericSubgroupPair :
    CyclicSubgroups EjBar.toAffine.Point N ≃
      {x : PairClasses Kbar N // pairJ x = algebraMap Qj Kbar RatFunc.X} := by
  let E := EjBar
  letI : E.IsElliptic := inferInstanceAs (Ej.baseChange Kbar).IsElliptic
  letI : CharZero Kbar := charZero_of_injective_algebraMap (algebraMap Qj Kbar).injective
  have hj : E.j = algebraMap Qj Kbar RatFunc.X :=
    (Ej.map_j (algebraMap Qj Kbar)).trans (congrArg (algebraMap Qj Kbar) Ej_j)
  have hj₀ : E.j ≠ 0 := by
    rw [hj, ← map_zero (algebraMap Qj Kbar)]
    exact (algebraMap Qj Kbar).injective.ne RatFunc.X_ne_zero
  have hj₁ : E.j ≠ 1728 := by
    rw [hj, ← map_ofNat (algebraMap Qj Kbar) 1728]
    exact (algebraMap Qj Kbar).injective.ne (sub_ne_zero.mp X_sub_1728_ne_zero)
  exact (Equiv.ofBijective (subgroupPair E)
    ⟨subgroupPair_injective E hj₀ hj₁, subgroupPair_surjective E⟩).trans
      (Equiv.subtypeEquivRight fun x => hj ▸ Iff.rfl)

/-- Identify the pinned geometric point with the subgroup on the actual `EjBar`.
The stabilizer of a representative at the indeterminate j fixes every subgroup,
so transport to this equation is independent of the chosen isomorphism. -/
noncomputable def genericJSubgroups :
    (Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) ≃ CyclicSubgroups EjBar.toAffine.Point N :=
  (genericJPairClasses h₂).trans genericSubgroupPair.symm

/-- The subgroup on `EjBar` represents the pinned pair class. -/
theorem genericJSubgroups_pairClass (x : Y0RationalGenericJ h₂ →ₐ[Qj] Kbar) :
    (Quot.mk _ (⟨EjBar, inferInstanceAs (Ej.baseChange Kbar).IsElliptic,
      genericJSubgroups h₂ x⟩ : EnhancedCurve Kbar N) : PairClasses Kbar N) =
      rationalPoints h₂ (genericJPointsOnRational h₂ x).val := by
  exact congrArg Subtype.val (genericSubgroupPair.apply_symm_apply (genericJPairClasses h₂ x))

#print axioms genericJPointsOnRational
#print axioms genericJPointsOnRational_apply
#print axioms genericJPairClasses
#print axioms genericSubgroupPair
#print axioms genericJSubgroups
#print axioms genericJSubgroups_pairClass

end WeierstrassCurve.ModelLevels.ModelGeneric2
