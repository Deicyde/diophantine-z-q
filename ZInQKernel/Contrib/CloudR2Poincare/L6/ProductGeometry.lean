import ZInQKernel.Contrib.CloudR2Poincare.L6.HOneFaceInjection
/-! Genuine geometric integrality of a product over a field. The composition
step is proved through ACTUAL field pullbacks, native flat/open integral-family
geometry and proper Noetherian base change, not an assumed product property. -/
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- Geometric integrality of a genuine flat/open geometrically-integral family
composed with a proper geometrically-integral field scheme. -/
theorem nativeGeometricallyIntegral_comp_to_field
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsProper g] [GeometricallyIntegral g] : GeometricallyIntegral (f ≫ g) := by
  constructor
  intro K instK t Z a b h
  let sq := IsPullback.of_hasPullback g t
  let l : Z ⟶ pullback g t := sq.lift (a ≫ f) b (by rw [Category.assoc, h.w])
  have hs : IsPullback a l f (pullback.fst g t) := IsPullback.of_bot' h sq
  haveI : IsIntegral (pullback g t) :=
    GeometricallyIntegral.geometrically_isIntegral (f := g) t _ _ sq
  haveI : IsLocallyNoetherian (pullback g t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g t)
  haveI : GeometricallyIntegral l := MorphismProperty.of_isPullback hs inferInstance
  haveI : Flat l := MorphismProperty.of_isPullback hs inferInstance
  haveI : UniversallyOpen l := MorphismProperty.of_isPullback hs inferInstance
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian l

/-- The actual product of proper geometrically-integral field schemes is
geometrically integral over the ORIGINAL field (no supplied product premise). -/
theorem nativeProduct_geometricallyIntegral
    {k : Type u} [Field k] (X Y : Over (Spec (.of k)))
    [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] : GeometricallyIntegral (X ⊗ Y).hom := by
  haveI : Flat Y.hom := by infer_instance
  haveI : UniversallyOpen Y.hom := by infer_instance
  haveI : GeometricallyIntegral (fst X Y).left :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst X.hom Y.hom))
  haveI : Flat (fst X Y).left := inferInstanceAs (Flat (pullback.fst X.hom Y.hom))
  haveI : UniversallyOpen (fst X Y).left :=
    inferInstanceAs (UniversallyOpen (pullback.fst X.hom Y.hom))
  rw [← Over.w (fst X Y)]
  exact nativeGeometricallyIntegral_comp_to_field (fst X Y).left X.hom

end ZInQ.Contrib.CloudR2Poincare.L6
