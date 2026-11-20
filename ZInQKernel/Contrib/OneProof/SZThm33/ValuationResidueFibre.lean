import ZInQKernel.Contrib.OneProof.SZThm33.ValuationGenericFibre
import ZInQKernel.Contrib.OneProof.SZThm33.GeomTateSections

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup ZInQ.HeightSplit

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O)

/-- The geometric residue point of the valuation ring using the fixed
identification of its residue field with the model's geometric residue field. -/
def valuationGeometricResidue : Spec (CommRingCat.of (ResBarO O)) ⟶ Spec (CommRingCat.of w) :=
  (Spec.map (CommRingCat.ofHom (RingEquiv.toRingHom (geomResidueEquiv hw)))) ≫ res

theorem valuationGeometricResidue_comp_base :
    valuationGeometricResidue hw ≫ base hw = (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) := by
  rw [valuationGeometricResidue, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : O →+* (ResBarO O) => Spec.map (CommRingCat.ofHom f)) (geomResidueEquiv_comp hw)

theorem valuationGeometricResidue_eq :
    valuationGeometricResidue hw =
      Spec.map (CommRingCat.ofHom ((geomResidueEquiv hw).toRingHom.comp (IsLocalRing.residue w))) :=
  (Spec.map_comp _ _).symm

private theorem residueIso_cancel :
    (Spec.map (CommRingCat.ofHom (RingEquiv.toRingHom (geomResidueEquiv hw)))) ≫ Spec.map (CommRingCat.ofHom (geomResidueEquiv hw).symm.toRingHom) =
      𝟙 (Spec (CommRingCat.of (ResBarO O))) := by
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (geomResidueEquiv hw).symm.toRingHom ≫
      CommRingCat.ofHom (geomResidueEquiv hw).toRingHom = 𝟙 (CommRingCat.of (ResBarO O)) := by
    ext a
    exact (geomResidueEquiv hw).apply_symm_apply a
  rw [h, Spec.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- An ambient valuation section with the specified geometric residue point
specializes to that point after projection to the original model. -/
theorem valuationSection_specializes (x : Over.mk (base hw) ⟶ M.G)
    (y : (algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M)
    (h : restrictPoint res x = geomSpecialPointEquiv hw A M y) :
    valuationGeometricResidue hw ≫ (valuationSectionEquiv hw A M x).left ≫
        pullback.fst M.G.hom (base hw) = y.left ≫ pullback.fst M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) := by
  have h' : res ≫ x.left = (geomSpecialPointEquiv hw A M y).left :=
    congrArg Over.Hom.left h
  rw [geomSpecialPointEquiv_left] at h'
  rw [valuationSectionEquiv_fst, valuationGeometricResidue, Category.assoc, h',
    ← Category.assoc (Spec.map (CommRingCat.ofHom (RingEquiv.toRingHom (geomResidueEquiv hw)))), residueIso_cancel, Category.id_comp]

private def fromUnitOver {S : Scheme.{0}} {r : S ⟶ S} (hr : r = 𝟙 S) :
    𝟙_ (Over S) ⟶ Over.mk r :=
  Over.homMk (𝟙 S) (by change (𝟙 S) ≫ r = 𝟙 S; rw [Category.id_comp, hr])

private theorem selfSpecMap (k : Type) [Field k] :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

private def precomposeSection {S : Scheme.{0}} {A B Y : Over S} [GrpObj Y] (i : A ⟶ B) :
    (B ⟶ Y) →* (A ⟶ Y) := ((yonedaMon.obj (.mk Y)).map i.op).hom

private theorem precomposeSection_left {S : Scheme.{0}} {r : S ⟶ S} {Y : Over S} [GrpObj Y]
    (hr : r = 𝟙 S) (x : Over.mk r ⟶ Y) :
    (precomposeSection (fromUnitOver hr) x).left = x.left :=
  Category.id_comp _

/-- Turn a geometric affine test point into a section over its own field. -/
def geometricSection {Y : Over (Spec (CommRingCat.of (ResBarO O)))} [GrpObj Y] :
    ((algPt (ResBarO O) (ResBarO O)) ⟶ Y) →* (𝟙_ (Over (Spec (CommRingCat.of (ResBarO O)))) ⟶ Y) :=
  precomposeSection (fromUnitOver (selfSpecMap (ResBarO O)))

theorem geometricSection_left {Y : Over (Spec (CommRingCat.of (ResBarO O)))} [GrpObj Y] (x : (algPt (ResBarO O) (ResBarO O)) ⟶ Y) :
    (geometricSection (O := O) x).left = x.left :=
  precomposeSection_left (selfSpecMap (ResBarO O)) x

end SZRaynaud.Ambient
