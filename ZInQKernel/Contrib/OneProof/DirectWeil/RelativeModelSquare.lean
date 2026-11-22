import ZInQKernel.Contrib.OneProof.NeronDVR.RelativePicard
import ZInQKernel.Contrib.OneProof.NeronDVR.UniversalSquare
import ZInQKernel.Contrib.OneProof.NeronDVR.LocalPicard

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Relative

open NeronDVR

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

abbrev genericMap (R K : Type) [CommRing R] [Field K] [Algebra R K] :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

abbrev Generic (G : Over (Spec (.of R))) := (Over.pullback (genericMap R K)).obj G

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- The relative theorem of the square for a smooth group with geometrically
integral fibres and abelian generic fibre, using the actual line on the model. -/
theorem square_of_geometricallyIntegral (G : Over (Spec (.of R))) [GrpObj G]
    [Smooth G.hom] [GeometricallyIntegral G.hom] [IsProper (Generic (K := K) G).hom]
    (L : G.left.Pic) (a : 𝟙_ (Over (Spec (.of R))) ⟶ G) :
    Scheme.Pic.map (leftTranslationIso G a).hom.left L *
      Scheme.Pic.map (leftTranslationIso G a).inv.left L = L ^ 2 := by
  let j := genericMap R K
  let F := Over.pullback j
  let : GrpObj (F.obj G) := Functor.grpObjObj
  have : Smooth (F.obj G).hom := show Smooth (pullback.snd G.hom j) by infer_instance
  have : GeometricallyIntegral (F.obj G).hom :=
    show GeometricallyIntegral (pullback.snd G.hom j) by infer_instance
  let A : PkgI3.AbVar K := ⟨F.obj G⟩
  let X := G ⊗ G
  let f : X ⟶ G := fst G G
  let b : X ⟶ G := snd G G ≫ 𝟙 G
  let s : G ⟶ X := lift (𝟙 G) (toUnit G ≫ η[G])
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : Smooth f.left := show Smooth (pullback.fst G.hom G.hom) by infer_instance
  have : GeometricallyIntegral f.left :=
    show GeometricallyIntegral (pullback.fst G.hom G.hom) by infer_instance
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian f.left
  have hs : s.left ≫ f.left = 𝟙 G.left :=
    congrArg CommaMorphism.left (lift_fst (𝟙 G) (toUnit G ≫ η[G]))
  let C := translationSquareClass f b L
  have hS : Scheme.Pic.map s.left C = 1 := map_translationSquareClass_identitySlice G G (𝟙 G) L
  have hK : Scheme.Pic.map (pullback.fst (f.left ≫ G.hom) j) C = 1 := by
    rw [Over.w f]
    change Scheme.Pic.map (pullback.fst X.hom j) (translationSquareClass f b L) = 1
    rw [map_translationSquareClass_baseChange]
    exact translationSquareClass_eq_one_over_field A (F.obj X) (F.map f) (F.map b) _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hC : C = 1 :=
    GenericFrame.pic_eq_one_of_fractionField_and_section G.hom f.left s.left hs π hπ C hK hS
  have : Subsingleton (Spec (.of R)).Pic := Scheme.Pic.subsingleton_spec_localRing R
  simpa only [Category.comp_id] using picard_square_of_translationSquareClass_eq_one G G (𝟙 G) L hC a

end SZRaynaud.Relative
