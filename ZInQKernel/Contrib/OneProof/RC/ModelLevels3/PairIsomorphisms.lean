import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ShortIsomorphisms
import Mathlib.Logic.Relation

/-! # Composition of the isomorphisms defining cyclic pairs -/

namespace WeierstrassCurve.ModelLevels

open WeierstrassCurve.Affine

variable {k : Type*} [Field k] [DecidableEq k]

private theorem cast_mapAddSubgroup {W V : WeierstrassCurve k} (h : W = V)
    (C : AddSubgroup W.toAffine.Point) :
    (AddEquiv.cast (M := fun W : WeierstrassCurve k => W.toAffine.Point) h).mapAddSubgroup C =
      h ▸ C := by
  cases h
  exact AddSubgroup.map_id C

/-- A change of variables viewed as an isomorphism of point groups
between the two indicated equations. -/
def changePoints (W V : WeierstrassCurve k) (v : VariableChange k) (h : v • W = V) :
    W.toAffine.Point ≃+ V.toAffine.Point :=
  (Point.addEquivVariableChange W v).symm.trans (AddEquiv.cast h)

private theorem mapAddSubgroup_trans {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (f : A ≃+ B) (g : B ≃+ C) (H : AddSubgroup A) :
    (f.trans g).mapAddSubgroup H = g.mapAddSubgroup (f.mapAddSubgroup H) :=
  (AddSubgroup.map_map H g.toAddMonoidHom f.toAddMonoidHom).symm

theorem changePoints_mapAddSubgroup_iff (W V : WeierstrassCurve k) (v : VariableChange k)
    (h : v • W = V) (H : AddSubgroup W.toAffine.Point) (K : AddSubgroup V.toAffine.Point) :
    (changePoints W V v h).mapAddSubgroup H = K ↔
      (Point.addEquivVariableChange W v).symm.mapAddSubgroup H = h.symm ▸ K := by
  cases h
  rw [changePoints, mapAddSubgroup_trans, cast_mapAddSubgroup]

theorem changePoints_one (W : WeierstrassCurve k) :
    changePoints W W 1 (one_smul _ _) = AddEquiv.refl _ := by
  apply AddEquiv.symm_bijective.injective
  ext P
  change Point.addEquivVariableChange W 1
    (cast (congrArg (fun V : WeierstrassCurve k => V.toAffine.Point) (one_smul _ W).symm) P) = P
  cases P with
  | zero => rw [← Point.zero_def, Point.cast_zero (one_smul (VariableChange k) W).symm, map_zero]
  | some x y h =>
    rw [Point.cast_some (one_smul (VariableChange k) W).symm, Point.coe_addEquivVariableChange,
      Point.equivVariableChange_some]
    simp [VariableChange.one_def]

theorem changePoints_comp (W V U : WeierstrassCurve k) (v w : VariableChange k)
    (hv : v • W = V) (hw : w • V = U) :
    (changePoints W V v hv).trans (changePoints V U w hw) =
      changePoints W U (w * v) ((mul_smul w v W).trans ((congrArg (w • ·) hv).trans hw)) := by
  subst V
  subst U
  apply AddEquiv.symm_bijective.injective
  ext P
  change Point.addEquivVariableChange W v (Point.addEquivVariableChange (v • W) w P) =
    Point.addEquivVariableChange W (w * v)
      (cast (congrArg (fun V : WeierstrassCurve k => V.toAffine.Point) (mul_smul w v W).symm) P)
  cases P with
  | zero => rw [← Point.zero_def, Point.cast_zero (mul_smul w v W).symm, map_zero, map_zero, map_zero]
  | some x y h =>
    rw [Point.cast_some (mul_smul w v W).symm]
    simp only [Point.coe_addEquivVariableChange, Point.equivVariableChange_some, Point.some.injEq,
      VariableChange.mul_def, Units.val_mul]
    constructor <;> ring

private theorem changePoints_inv (W V : WeierstrassCurve k) (v : VariableChange k)
    (h : v • W = V) :
    changePoints V W v⁻¹ ((congrArg (v⁻¹ • ·) h.symm).trans (inv_smul_smul _ _)) =
      (changePoints W V v h).symm := by
  let e := changePoints W V v h
  let d := changePoints V W v⁻¹ ((congrArg (v⁻¹ • ·) h.symm).trans (inv_smul_smul _ _))
  have he : e.trans d = AddEquiv.refl _ := by
    dsimp only [e, d]
    rw [changePoints_comp]
    have aux (a : VariableChange k) (ha : a = 1) (hh : a • W = W) :
        changePoints W W a hh = AddEquiv.refl _ := by
      subst a
      exact changePoints_one W
    exact aux _ (inv_mul_cancel v) _
  ext Q
  obtain ⟨P, rfl⟩ := e.surjective Q
  exact (DFunLike.congr_fun he P).trans (e.symm_apply_apply P).symm

/-- Equality in `PairClasses` is witnessed by a single
Weierstrass change of variables carrying one subgroup onto the other. -/
theorem pairClasses_eq_iff {N : ℕ} (A B : EnhancedCurve k N) :
    (Quot.mk _ A : PairClasses k N) = Quot.mk _ B ↔
      ∃ v : VariableChange k, ∃ h : v • A.equation = B.equation,
        (changePoints A.equation B.equation v h).mapAddSubgroup A.subgroup.val = B.subgroup.val := by
  let rel (A B : EnhancedCurve k N) :=
    ∃ v : VariableChange k, ∃ h : v • A.equation = B.equation,
      (changePoints A.equation B.equation v h).mapAddSubgroup A.subgroup.val = B.subgroup.val
  have hr : Equivalence rel := by
    constructor
    · intro X
      exact ⟨1, one_smul _ _, by rw [changePoints_one]; exact AddSubgroup.map_id _⟩
    · rintro X Y ⟨v, h, hv⟩
      refine ⟨v⁻¹, (congrArg (v⁻¹ • ·) h.symm).trans (inv_smul_smul _ _), ?_⟩
      rw [changePoints_inv X.equation Y.equation v h]
      exact (AddEquiv.mapAddSubgroup _).symm_apply_eq.mpr hv.symm
    · rintro X Y Z ⟨v, hv, hXY⟩ ⟨w, hw, hYZ⟩
      refine ⟨w * v, (mul_smul w v X.equation).trans ((congrArg (w • ·) hv).trans hw), ?_⟩
      rw [← changePoints_comp X.equation Y.equation Z.equation v w hv hw,
        mapAddSubgroup_trans, hXY, hYZ]
  constructor
  · intro h
    apply hr.eqvGen_iff.mp
    have hh := Quot.eqvGen_exact h
    refine Relation.EqvGen.mono (r := _) (p := rel) ?_ A B hh
    rintro X Y ⟨v, hv, hXY⟩
    exact ⟨v, hv, (changePoints_mapAddSubgroup_iff _ _ _ _ _ _).mpr hXY⟩
  · rintro ⟨v, hv, hXY⟩
    exact Quot.sound ⟨v, hv, (changePoints_mapAddSubgroup_iff _ _ _ _ _ _).mp hXY⟩

#print axioms cast_mapAddSubgroup
#print axioms changePoints
#print axioms mapAddSubgroup_trans
#print axioms changePoints_mapAddSubgroup_iff
#print axioms changePoints_one
#print axioms changePoints_comp
#print axioms changePoints_inv
#print axioms pairClasses_eq_iff

end WeierstrassCurve.ModelLevels
