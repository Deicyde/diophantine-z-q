import ZInQKernel.Contrib.OneProof.FaltingsDVR.StrictBaseChange

noncomputable section
open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SmoothGroup

private def unitOverMapIso {S T : Scheme.{0}} (d : T ⟶ S) :
    (Over.map d).obj (𝟙_ (Over T)) ≅ Over.mk d :=
  Over.isoMk (Iso.refl _) rfl

/-- Relative points and points of the pullback have the same group law. -/
def pullbackPointEquiv {S T : Scheme.{0}} (d : T ⟶ S) (X : Over S) [GrpObj X] :
    letI : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
    (Over.mk d ⟶ X) ≃* (𝟙_ (Over T) ⟶ (Over.pullback d).obj X) := by
  let : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
  let e := (Over.mapPullbackAdj d).homEquiv (𝟙_ (Over T)) X
  let t := unitOverMapIso d
  refine
    { toFun := fun a => e (t.hom ≫ a)
      invFun := fun a => t.inv ≫ e.symm a
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro a
    simp [Iso.inv_hom_id_assoc]
  · intro a
    simp [Iso.hom_inv_id_assoc]
  · intro a b
    rw [MonObj.comp_mul]
    change (Over.mapPullbackAdj d).homEquiv _ _ (_ * _) = _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]

theorem pullbackPointEquiv_naturality {S T : Scheme.{0}} (d : T ⟶ S)
    {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) (a : Over.mk d ⟶ X) :
    letI : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback d).obj Y) := Functor.grpObjObj
    pullbackPointEquiv d Y (a ≫ f) = pullbackPointEquiv d X a ≫ (Over.pullback d).map f := by
  change (Over.mapPullbackAdj d).homEquiv _ _ ((unitOverMapIso d).hom ≫ a ≫ f) = _
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl


open ReductSplit

/-- The geometric special fibre, taken after a strictly henselian base
extension. -/
abbrev geometricSpecialFibre {K E L : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E}
    (hP : P.comap (algebraMap K E) = O) [Field L]
    [Algebra (IsLocalRing.ResidueField P) L] :
    Over (Spec (.of O)) ⥤ Over (Spec (.of L)) :=
  Over.pullback (comapSpec hP) ⋙
    Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField P) L)) ≫
      (residueObject P).hom)

set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- The canonical comparison has no prime-to-residue-characteristic torsion
in its kernel on the geometric special-fibre group itself. -/
theorem geometric_special_map_torsion_kernel_trivial
    {K E L : Type} [Field K] [Field E] [Algebra K E] [Field L]
    {O : ValuationSubring K} {P : ValuationSubring E}
    (hP : P.comap (algebraMap K E) = O)
    [IsDiscreteValuationRing P] [HenselianLocalRing P]
    [IsSepClosed (IsLocalRing.ResidueField P)]
    [Algebra (IsLocalRing.ResidueField P) L]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField P) L]
    {A : PkgI3.AbVar K} (G N : GroupModelO A O) (i : G.G ⟶ N.G)
    (hi : (Over.pullback (jO O)).map i ≫ N.gen.hom = G.gen.hom) :
    let J := Over.pullback (comapSpec hP)
    let F := Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField P) L)) ≫ (residueObject P).hom)
    letI : GrpObj (J.obj G.G) := Functor.grpObjObj
    letI : GrpObj (J.obj N.G) := Functor.grpObjObj
    letI : GrpObj (F.obj (J.obj G.G)) := Functor.grpObjObj
    letI : GrpObj (F.obj (J.obj N.G)) := Functor.grpObjObj
    ∀ (a : 𝟙_ (Over (Spec (.of L))) ⟶ F.obj (J.obj G.G)) (m : ℕ),
      IsUnit (m : O) → a ^ m = 1 → a ≫ F.map (J.map i) = 1 → a = 1 := by
  dsimp only
  intro a m hm ha hg
  let J := Over.pullback (comapSpec hP)
  let d := Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField P) L)) ≫
    (residueObject P).hom
  let : GrpObj (J.obj G.G) := Functor.grpObjObj
  let : GrpObj (J.obj N.G) := Functor.grpObjObj
  let : GrpObj ((Over.pullback d).obj (J.obj G.G)) := Functor.grpObjObj
  let : GrpObj ((Over.pullback d).obj (J.obj N.G)) := Functor.grpObjObj
  let e := pullbackPointEquiv d (J.obj G.G)
  let f := pullbackPointEquiv d (J.obj N.G)
  let b := e.symm a
  have hb : b ^ m = 1 := by
    change (e.symm a) ^ m = 1
    rw [← map_pow, ha, map_one]
  have hkernel : b ≫ J.map i = 1 := by
    apply f.injective
    rw [map_one]
    change pullbackPointEquiv d (J.obj N.G) (b ≫ J.map i) = 1
    rw [pullbackPointEquiv_naturality]
    change e (e.symm a) ≫ (Over.pullback d).map (J.map i) = 1
    rw [MulEquiv.apply_symm_apply]
    exact hg
  have hb1 : b = 1 :=
    geometric_special_torsion_kernel_trivial_of_comparison hP G N i hi b m hm hb hkernel
  have h := congrArg e hb1
  change e (e.symm a) = e 1 at h
  simpa only [MulEquiv.apply_symm_apply, map_one] using h

end SmoothGroup
