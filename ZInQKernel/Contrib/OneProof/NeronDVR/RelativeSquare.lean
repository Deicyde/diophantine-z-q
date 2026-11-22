import ZInQKernel.Contrib.OneProof.NeronDVR.LocalPicard
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativePicard
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquareReduction
import ZInQKernel.Contrib.OneProof.NeronDVR.UniversalSquare

/-!
# The relative square on the strict Néron model

The square class on the product of the model with its identity subgroup
is trivial on the generic fibre by the cube identity. It is normalized
on the identity slice. Picard detection by these two restrictions makes
the class trivial globally.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules CategoryTheory.MonObj

namespace NeronDVR

open ZInQ.Contrib.GroupLawNeron CToPrinted

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
/-- The relative square identity required for the strict Néron model. -/
theorem relativeSquareStrictNeron : RelativeSquareStrictNeron := by
  intro R K _ _ _ _ _ _ _ _ G _ hG A e D hD
  dsimp only
  intro a ha
  let S := Spec (CommRingCat.of R)
  let j := genMap R K
  let F := Over.pullback j
  let B₀ := F.obj G
  have : Smooth G.hom := hG.1
  have : QuasiCompact G.hom := hG.2.2.2.1
  have : Smooth B₀.hom := show Smooth (pullback.snd G.hom j) by infer_instance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
  have : IsProper A.X.hom := A.proper
  have : GeometricallyIntegral A.X.hom := A.geomInt
  have : IsProper B₀.hom := by rw [← Over.w e.hom]; infer_instance
  have : GeometricallyIntegral B₀.hom := by rw [← Over.w e.hom]; infer_instance
  let B : PkgI3.AbVar K :=
    { X := B₀
      grp := Functor.grpObjObj
      proper := inferInstance
      smooth := inferInstance
      geomInt := inferInstance }
  have : IsIntegral (pullback G.hom j) :=
    GeometricallyIntegral.isIntegral_of_subsingleton B₀.hom
  have : IsIntegral G.left := isIntegral_of_integral_generic_fibre (K := K) G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨H, _, i, _, _, _, _, _, hRange⟩ :=
    exists_identitySubgroup_dvr G (algebraMap R K) (IsFractionRing.injective R K)
      (by infer_instance)
  let X : Over S := G ⊗ H
  let f : X ⟶ G := fst G H
  let b : X ⟶ G := snd G H ≫ i
  let s : G ⟶ X := lift (𝟙 G) (toUnit G ≫ η[H])
  have : Smooth f.left := show Smooth (pullback.fst G.hom H.hom) by infer_instance
  have : GeometricallyIntegral f.left :=
    show GeometricallyIntegral (pullback.fst G.hom H.hom) by infer_instance
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian f.left
  let := hD.isInvertible_dual_toModules
  let L := Scheme.Pic.mk D.toModulesᵛ
  let C := translationSquareClass f b L
  have hs : s.left ≫ f.left = 𝟙 G.left :=
    congrArg CommaMorphism.left (lift_fst (𝟙 G) (toUnit G ≫ η[H]))
  have hS : Scheme.Pic.map s.left C = 1 := map_translationSquareClass_identitySlice G H i L
  have hK : Scheme.Pic.map (pullback.fst (f.left ≫ G.hom) j) C = 1 := by
    rw [Over.w f]
    change Scheme.Pic.map (pullback.fst X.hom j) (translationSquareClass f b L) = 1
    rw [map_translationSquareClass_baseChange]
    exact translationSquareClass_eq_one_over_field B (F.obj X) (F.map f) (F.map b) _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hC : C = 1 :=
    GenericFrame.pic_eq_one_of_fractionField_and_section G.hom f.left s.left hs π hπ C hK hS
  have : Subsingleton S.Pic := Scheme.Pic.subsingleton_spec_localRing R
  have ha' : a.left (IsLocalRing.closedPoint R) ∈ Set.range i.left := hRange.symm ▸ ha
  obtain ⟨c, hc⟩ := exists_section_of_closed_mem_open_subgroup i a ha'
  simpa only [hc] using picard_square_of_translationSquareClass_eq_one G H i L hC c

/-- Néron models over Dedekind domains, with the prescribed generic fibre
and the Néron mapping property. -/
theorem neronSchemeExtensionDedekind_proof : NeronSchemeExtensionDedekind :=
  neronSchemeExtensionDedekind_of_relativeSquare relativeSquareStrictNeron

end NeronDVR
