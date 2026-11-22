import ZInQKernel.Contrib.OneProof.FaltingsDVR.PullbackPoints
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SmoothGroup

open ReductSplit ReductGlue ZInQ.FaltingsRestate ZInQ.SemiAbDescend

/-- The canonical morphism from the algebraically closed special point. -/
abbrev geometricPoint {K : Type} [Field K] (O : ValuationSubring K) :
    Spec (.of (ResBarO O)) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- For the canonical comparison over a DVR, the kernel of the special-fibre
map over the algebraic closure has no nonidentity prime-to-characteristic
torsion points. -/
theorem torsion_kernel_trivial_over_geometricPoint
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G N : GroupModelO A O) (i : G.G ⟶ N.G)
    (hi : (Over.pullback (jO O)).map i ≫ N.gen.hom = G.gen.hom) :
    let F := Over.pullback (geometricPoint O)
    letI : GrpObj (F.obj G.G) := Functor.grpObjObj
    letI : GrpObj (F.obj N.G) := Functor.grpObjObj
    ∀ (a : 𝟙_ (Over (Spec (.of (ResBarO O)))) ⟶ F.obj G.G) (m : ℕ),
      (m : ResBarO O) ≠ 0 → a ^ m = 1 → a ≫ F.map i = 1 → a = 1 := by
  dsimp only
  intro a m hm ha hk
  obtain ⟨w, hw⟩ := GapSHPair.exists_comap_eq (Ω := AlgebraicClosure K) O
  let E := GapSHPair.inertiaField (K := K) w
  let P := GapSHPair.wE (K := K) w
  have hP : P.comap (algebraMap K E) = O := GapSHPair.hE_eq w hw
  have hs := GapSHPair.isSHSep_inertia w hw
  have : IsDiscreteValuationRing P := hs.1.1
  have : HenselianLocalRing P := hs.1.2.1
  have : IsSepClosed (IsLocalRing.ResidueField P) := hs.1.2.2
  let k := IsLocalRing.ResidueField O
  let k' := IsLocalRing.ResidueField P
  let L := ResBarO O
  let : Algebra k k' := (resMap hP).toAlgebra
  have : Algebra.IsSeparable k k' := hs.2.2.2
  have : Algebra.IsAlgebraic k k' := Algebra.IsSeparable.isAlgebraic _ _
  let φ : k' →ₐ[k] L := IsAlgClosed.lift
  let : Algebra k' L := φ.toRingHom.toAlgebra
  have : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun x =>
    (φ.commutes x).symm
  have : Algebra.IsAlgebraic k' L := Algebra.IsAlgebraic.tower_top (K := k) k'
  let J := Over.pullback (comapSpec hP)
  let d := Spec.map (CommRingCat.ofHom (algebraMap k' L)) ≫ (residueObject P).hom
  let F := Over.pullback d
  let H := Over.pullback (geometricPoint O)
  have hd : d ≫ comapSpec hP = geometricPoint O := by
    change (Spec.map (CommRingCat.ofHom (algebraMap k' L)) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue P))) ≫
      Spec.map (CommRingCat.ofHom (comapHom hP)) =
        Spec.map (CommRingCat.ofHom (algebraMap O L))
    rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change φ (IsLocalRing.residue P (comapHom hP x)) = algebraMap O L x
    rw [← resMap_residue, IsScalarTower.algebraMap_apply O k L]
    exact φ.commutes (IsLocalRing.residue O x)
  let : GrpObj (J.obj G.G) := Functor.grpObjObj
  let : GrpObj (J.obj N.G) := Functor.grpObjObj
  let : GrpObj (F.obj (J.obj G.G)) := Functor.grpObjObj
  let : GrpObj (F.obj (J.obj N.G)) := Functor.grpObjObj
  let : GrpObj (H.obj G.G) := Functor.grpObjObj
  let : GrpObj (H.obj N.G) := Functor.grpObjObj
  let geomG := pbCompIso d (comapSpec hP) (geometricPoint O) hd (Grp.mk G.G)
  let geomN := pbCompIso d (comapSpec hP) (geometricPoint O) hd (Grp.mk N.G)
  let eG : F.obj (J.obj G.G) ≅ H.obj G.G := isoX geomG
  let eN : F.obj (J.obj N.G) ≅ H.obj N.G := isoX geomN
  have : IsMonHom eG.inv := geomG.inv.hom.isMonHom_hom
  have : IsMonHom eN.hom := geomN.hom.hom.isMonHom_hom
  let j := Over.pullback (jO O)
  let : GrpObj (j.obj G.G) := Functor.grpObjObj
  let : GrpObj (j.obj N.G) := Functor.grpObjObj
  have : IsMonHom N.gen.hom := N.gen_hom
  have : IsMonHom (j.map i ≫ N.gen.hom) := hi ▸ G.gen_hom
  have : IsMonHom (j.map i) := isMonHom_of_comp_mono _ N.gen.hom
  have : IsMonHom i := isMonHom_of_generic G N i (j.map i) inferInstance rfl
  have hnat : F.map (J.map i) ≫ eN.hom = eG.hom ≫ H.map i :=
    pbCompIso_natural' d (comapSpec hP) (geometricPoint O) hd i
  have hu : IsUnit (m : O) := by
    apply isUnit_of_map_unit (IsLocalRing.residue O)
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hm
    have h := congrArg (algebraMap k L) hz
    simpa only [map_natCast, map_zero] using h
  let b := a ≫ eG.inv
  have hb : b ^ m = 1 := by
    change (a ≫ eG.inv) ^ m = 1
    rw [← MonObj.pow_comp, ha, MonObj.one_comp]
  have hbK : b ≫ F.map (J.map i) = 1 := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, hnat, MonObj.one_comp]
    change (a ≫ eG.inv) ≫ eG.hom ≫ H.map i = 1
    rw [Category.assoc, eG.inv_hom_id_assoc]
    exact hk
  have hb1 : b = 1 :=
    geometric_special_map_torsion_kernel_trivial hP G N i hi b m hu hb hbK
  apply (cancel_mono eG.inv).mp
  rw [MonObj.one_comp]
  exact hb1

end SmoothGroup
