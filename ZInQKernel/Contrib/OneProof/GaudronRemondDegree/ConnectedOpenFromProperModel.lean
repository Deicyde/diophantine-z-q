import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.ProperRestriction
import ZInQKernel.Contrib.CloudW02Connectedness.Basic

/-! # Geometrically connected fibers over a nonempty open of the original model -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped NumberField

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue
open ZInQ.Contrib.SpreadOut ZInQ.Contrib.EGAProperLimit

/-- The original model, after a factorial localization that makes it proper, has
geometrically connected fibers by the already-formalized Zariski connectedness theorem. -/
theorem originalModel_geometricallyConnected_localization {K L : Type} [Field K] [Field L]
    [NumberField L] [Algebra K L] {A : PkgI3.AbVar K} (N : GroupModel A L) (n : ℕ)
    (hp : IsProper ((Over.pullback (modelLocalizationMap L n)).obj N.G).hom) :
    GeometricallyConnected ((Over.pullback (modelLocalizationMap L n)).obj N.G).hom := by
  let R := NF.Rg L n
  letI : Algebra R L := (NF.toL L n).toAlgebra
  letI : IsScalarTower (𝓞 L) R L :=
    IsScalarTower.of_algebraMap_eq (fun x => (NF.toL_alg L n x).symm)
  let X : Over (Spec (CommRingCat.of R)) := (Over.pullback (modelLocalizationMap L n)).obj N.G
  let g : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R L))
  have hw : g ≫ modelLocalizationMap L n = jL L := modelLocalization_generic_comp L n
  let e : (Over.pullback g).obj X ≅ (A.baseChange L).X :=
    ((pbNat _ _ _ hw).app N.G) ≪≫ N.gen
  let e' := (Over.forget _).mapIso e
  have hEq : e'.hom ≫ (A.baseChange L).X.hom = ((Over.pullback g).obj X).hom := Over.w e.hom
  have hgen : GeometricallyConnected ((Over.pullback g).obj X).hom := by
    rw [← hEq]
    have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected) e'.hom
      (A.baseChange L).X.hom).mpr (geomConnected_of_geomIntegral _ (A.baseChange L).geomInt)
  letI : Smooth N.G.hom := N.smooth
  have hs : Smooth X.hom :=
    show Smooth (pullback.snd N.G.hom (modelLocalizationMap L n)) from inferInstance
  exact ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness
    ZariskiConn.ZariskiConnectedness_proof L (NF.sf L n) R X hs hp hgen

/-- Supply the exact open used to construct the global marked identity-component model.
The restriction is of `N.G.hom` itself; neither a new model nor a spreading premise is used. -/
theorem connectedOpenOfGroupModels_proof
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (A : PkgI3.AbVar K) (N : GroupModel A L) :
    ∃ V : (Spec (CommRingCat.of (𝓞 L))).Opens,
      (V : Set (Spec (CommRingCat.of (𝓞 L)))).Nonempty ∧
        GeometricallyConnected (N.G.hom ∣_ V) := by
  obtain ⟨n, hp⟩ := originalModel_exists_properLocalization N
  let S := Spec (CommRingCat.of (𝓞 L))
  let U : S.Opens := PrimeSpectrum.basicOpen (NF.sf L n)
  let e : U.toScheme ≅ (NF.specDiag L).obj (Opposite.op n) :=
    basicOpenIsoSpecAway (R := CommRingCat.of (𝓞 L)) (NF.sf L n)
  have he : e.hom ≫ modelLocalizationMap L n = U.ι := basicOpenIsoSpecAway_hom_SpecMap
    (R := CommRingCat.of (𝓞 L)) (NF.sf L n)
  let X := (Over.pullback (modelLocalizationMap L n)).obj N.G
  letI : GeometricallyConnected X.hom := originalModel_geometricallyConnected_localization N n hp
  letI : GeometricallyConnected ((Over.pullback e.hom).obj X).hom :=
    show GeometricallyConnected (pullback.snd X.hom e.hom) from inferInstance
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let i := (Over.forget _).mapIso ((pbNat _ _ _ he).app N.G)
  have hi : i.hom ≫ pullback.snd N.G.hom U.ι = ((Over.pullback e.hom).obj X).hom :=
    Over.w (((pbNat _ _ _ he).app N.G).hom)
  have hpU : GeometricallyConnected (pullback.snd N.G.hom U.ι) :=
    (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected) i.hom _).mp
      (hi.symm ▸ (inferInstance : GeometricallyConnected ((Over.pullback e.hom).obj X).hom))
  refine ⟨U, ?_, (prop_pullbackSnd_iff (@GeometricallyConnected)
    (isPullback_morphismRestrict N.G.hom U).flip).mp hpU⟩
  refine ⟨(⊥ : PrimeSpectrum (𝓞 L)), ?_⟩
  change (⊥ : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.basicOpen (NF.sf L n)
  apply (PrimeSpectrum.mem_basicOpen _ _).2
  change NF.sf L n ∉ (⊥ : Ideal (𝓞 L))
  simpa only [Ideal.mem_bot] using NF.sf_ne_zero L n

end ZInQ.Contrib.IsogenyDegree
