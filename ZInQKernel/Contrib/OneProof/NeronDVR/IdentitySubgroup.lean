import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.NeronDVR.GroupAmple
import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR
import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open CToPrinted
open scoped AlgebraicGeometry.Scheme.Modules CategoryTheory.MonObj

noncomputable section

namespace NeronDVR

private theorem geometricallyConnected_of_idCompOpen {S : Scheme.{0}} (G : Over S)
    [GrpObj G] (W : G.left.Opens) (hW : (W : Set G.left) = idCompSet G)
    [LocallyOfFiniteType (W.ι ≫ G.hom)] [QuasiCompact (W.ι ≫ G.hom)] :
    GeometricallyConnected (W.ι ≫ G.hom) := by
  let f : W.toScheme ⟶ S := W.ι ≫ G.hom
  change GeometricallyConnected f
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro y
  have hV : ∀ x, (x ∈ W ∧ G.hom x = y) ↔
      x ∈ connectedComponentIn (G.hom ⁻¹' {y}) ((η[G] : 𝟙_ (Over S) ⟶ G).left y) := by
    intro x
    have hWx : x ∈ W ↔ x ∈ idCompSet G := Set.ext_iff.mp hW x
    constructor
    · rintro ⟨hx, hxy⟩
      have hx' := hWx.mp hx
      rw [idCompSet, Set.mem_ofPred_eq, show G.hom.base x = y from hxy] at hx'
      exact hx'
    · intro hx
      have hxy : G.hom x = y := by
        exact (show x ∈ G.hom ⁻¹' {y} from connectedComponentIn_subset _ _ hx)
      refine ⟨hWx.mpr ?_, hxy⟩
      rw [idCompSet, Set.mem_ofPred_eq, show G.hom.base x = y from hxy]
      exact hx
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ φ => ?_⟩
  have hc := SGA3Nbhd.connected_fibre_V geomConnOfRationalPoint_proof G W y hV
    (fun t => (Set.ext_iff.mp hW _).mpr (idCompSet_one G t)) φ
  exact (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f (S.fromSpecResidueField y) φ)).connectedSpace_iff.mpr hc

/-- The identity component of a smooth finite type group with connected generic fibre over a
DVR is an open smooth subgroup with geometrically integral fibres. -/
theorem exists_identitySubgroup_dvr {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] [QuasiCompact G.hom]
    {K : Type} [Field K] (φ : R →+* K) (hφ : Function.Injective φ)
    (hG : ConnectedSpace ↥(pullback G.hom (Spec.map (CommRingCat.ofHom φ)))) :
    ∃ (H : Over (Spec (CommRingCat.of R))) (_ : GrpObj H) (i : H ⟶ G),
      IsMonHom i ∧ IsOpenImmersion i.left ∧
      Smooth H.hom ∧ GeometricallyIntegral H.hom ∧ QuasiCompact H.hom ∧
      Set.range i.left = idCompSet G := by
  let S := Spec (CommRingCat.of R)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := (quasiCompact_iff_compactSpace G.hom).mp inferInstance
  have : IsNoetherian G.left := {}
  let W : G.left.Opens := ⟨idCompSet G, SGA3Nbhd.isOpen_idCompSet_dvr G φ hφ hG.isPreconnected_univ⟩
  have hgrp := SGA3Nbhd.idCompSubgroup_proof geomConnOfRationalPoint_proof S G
  have hW : OpenSub.IsSubgroupOpen G W := ⟨idCompSet_one G, hgrp.1, hgrp.2⟩
  let H := OpenSub.G0 W
  let : GrpObj H := OpenSub.grpG0 hW
  have hs : Smooth (W.ι ≫ G.hom) := inferInstance
  have : CompactSpace W := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (W : Set G.left))
  have hqc : QuasiCompact (W.ι ≫ G.hom) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have hg : GeometricallyConnected (W.ι ≫ G.hom) := geometricallyConnected_of_idCompOpen G W rfl
  have hi : GeometricallyIntegral (W.ι ≫ G.hom) := TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _
  exact ⟨H, inferInstance, OpenSub.incl W, OpenSub.isMonHom_incl hW, (show IsOpenImmersion W.ι from inferInstance),
    hs, hi, hqc, W.range_ι⟩

set_option backward.isDefEq.respectTransparency false in
/-- The generic fibre inclusion over a DVR is an open immersion. -/
theorem isOpenImmersion_fiberι_generic_dvr {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) :
    IsOpenImmersion (f.fiberι (⊥ : PrimeSpectrum R)) := by
  let p : PrimeSpectrum R := ⊥
  have hp : IsFractionRing R p.asIdeal.ResidueField :=
    inferInstanceAs (IsFractionRing R (⊥ : Ideal R).ResidueField)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hl : IsLocalization.Away π p.asIdeal.ResidueField :=
    ZInQ.Contrib.CloudR2NeronExistence.Henselian.NeronModelInfra.isLocalizationAway_of_irreducible
      p.asIdeal.ResidueField hπ
  have h₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap R p.asIdeal.ResidueField))) := IsOpenImmersion.of_isLocalization π
  have h₂ : IsOpenImmersion ((Spec (CommRingCat.of R)).fromSpecResidueField p) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of R) p]
    infer_instance
  exact show IsOpenImmersion (pullback.fst f ((Spec (CommRingCat.of R)).fromSpecResidueField p))
    from inferInstance

/-- The relative square identity for translations by the identity subgroup
turns a fibre-dense affine complement into an affine nonvanishing cover. -/
theorem exists_affine_nonvanishing_cover_of_relative_square
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom] [QuasiCompact G.hom]
    [G.left.IsSeparated]
    (hG : ConnectedSpace ↥(pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (D : G.left.IdealSheafData) (hD : D.IsInvertible) (hU : IsAffineOpen D.support.compl)
    (hDense : ∀ x : G.left, (∀ y, y ⤳ x → G.hom y = G.hom x → y = x) →
      x ∈ D.support.compl)
    (hSquare : letI := hD.isInvertible_dual_toModules
      let L := Scheme.Pic.mk D.toModulesᵛ
      ∀ (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G),
        a.left (IsLocalRing.closedPoint R) ∈ idCompSet G →
        Scheme.Pic.map (leftTranslationIso G a).hom.left L *
          Scheme.Pic.map (leftTranslationIso G a).inv.left L = L ^ 2) :
    letI := hD.isInvertible_dual_toModules
    ∀ x : G.left, ∃ s : 𝟙_ G.left.Modules ⟶ D.toModulesᵛ.tensorPow 2,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl := by
  obtain ⟨H, _, i, _, _, _, _, _, hi⟩ :=
    exists_identitySubgroup_dvr G (algebraMap R K) (IsFractionRing.injective R K) hG
  have : IsOpenImmersion (H.hom.fiberι (⊥ : PrimeSpectrum R)) :=
    isOpenImmersion_fiberι_generic_dvr H.hom
  let g (a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ H) : G.left ≅ G.left :=
    (Over.forget _).mapIso (leftTranslationIso G (a ≫ i))
  refine exists_affine_nonvanishing_of_symmetricTranslate_cover D hD hU g ?_ ?_
  · dsimp only
    intro a
    apply hSquare (a ≫ i)
    rw [← hi]
    exact ⟨a.left (IsLocalRing.closedPoint R), rfl⟩
  · intro x
    obtain ⟨a, ha, ha'⟩ := symmetricTranslation_cover_of_orbits i D.support.compl
      (leftOrbit_nonempty_of_contains_fibre_generics i D.support.compl hDense) x
    refine ⟨a, ?_⟩
    rw [symmetricTranslate_compl]
    exact ⟨ha, ha'⟩

end NeronDVR
