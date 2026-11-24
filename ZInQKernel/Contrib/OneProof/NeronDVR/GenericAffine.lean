import ZInQKernel.Contrib.OneProof.NeronDVR.AffineCompletion
import ZInQKernel.Contrib.OneProof.NeronDVR.StableAffine
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR

/-!
# A fibre-dense invariant affine open in a Néron model

The generic restriction of the canonical datum is a finite flat map to the
prescribed generic fibre. Completion of a suitable generic open gives an
invariant quasi-affine open. Descend that open and pull back a common affine
neighborhood of the images of the generic points of the fibres.
-/

open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra (specGenericFibreInclusion)

namespace NeronDVR

private theorem range_specGenericFibreInclusion (R K : Type) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Set.range (specGenericFibreInclusion R K) = {(⊥ : PrimeSpectrum R)} := by
  have key (x : PrimeSpectrum K) : specGenericFibreInclusion R K x = (⊥ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change x.asIdeal.comap (algebraMap R K) = ⊥
    rw [Ideal.eq_bot_of_prime x.asIdeal, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · rintro (rfl : x = (⊥ : PrimeSpectrum R))
    exact ⟨(⊥ : PrimeSpectrum K), key (⊥ : PrimeSpectrum K)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionToGeneric_left {S S' T T' : Scheme.{0}}
    (j : T ⟶ S) (p : S' ⟶ S) (N : Over S')
    (j' : T' ⟶ S') (t : T' ⟶ T) (hpb : IsPullback j' t p j)
    {A : Over T} (e : (Over.pullback j').obj N ≅ (Over.pullback t).obj A) :
    (restrictionToGeneric j p N j' t hpb e).left =
      ((genericFibreComparison j p j' t hpb).inv.app N).left ≫ e.hom.left ≫ pullback.fst A.hom t := by
  simp only [restrictionToGeneric, Adjunction.homEquiv_counit, Over.comp_left,
    Over.map_map_left, Over.mapPullbackAdj_counit_app, Over.homMk_left]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical descent datum of a Néron model over a smooth cover of
DVRs has an invariant affine open containing every generic point of a fibre. -/
theorem neronDescentDatum_exists_invariant_affine_open
    {R R' K K' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K]
    [Algebra R' K'] [IsFractionRing R' K']
    (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
    (hpb : IsPullback (specGenericFibreInclusion R' K') t p (specGenericFibreInclusion R K))
    [Smooth p] [Surjective p] [QuasiCompact p]
    (N : Over (Spec (CommRingCat.of R'))) [Smooth N.hom] [IsSeparated N.hom] [QuasiCompact N.hom]
    (A : Over (Spec (CommRingCat.of K)))
    (e : (Over.pullback (specGenericFibreInclusion R' K')).obj N ≅ (Over.pullback t).obj A)
    (hex : ∀ (Y : Over (Spec (CommRingCat.of R'))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (specGenericFibreInclusion R' K')).map f)) :
    let d := neronDescentDatum (specGenericFibreInclusion R K) p N (specGenericFibreInclusion R' K') t hpb e hex
    ∃ U : N.left.Opens, d.IsInvariant U ∧ IsAffineOpen U ∧
      ∀ x : N.left, (∀ y : N.left, y ⤳ x → N.hom y = N.hom x → y = x) → x ∈ U := by
  let j := specGenericFibreInclusion R K
  let j' := specGenericFibreInclusion R' K'
  let d := neronDescentDatum j p N j' t hpb e hex
  let r := (restrictionToGeneric j p N j' t hpb e).left
  have : IsOpenImmersion j := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have : IsLocalization.Away ϖ K :=
      ZInQ.Contrib.CloudR2NeronExistence.Henselian.NeronModelInfra.isLocalizationAway_of_irreducible K hϖ
    exact IsOpenImmersion.of_isLocalization ϖ
  have : Flat t := MorphismProperty.of_isPullback hpb (inferInstance : Flat p)
  have hft : LocallyOfFiniteType t :=
    MorphismProperty.of_isPullback hpb (inferInstance : LocallyOfFiniteType p)
  have : IsFinite t := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr hft
  have : IsIso ((genericFibreComparison j p j' t hpb).inv.app N).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((genericFibreComparison j p j' t hpb).inv.app N)))
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsFinite r := by
    change IsFinite (restrictionToGeneric j p N j' t hpb e).left
    rw [restrictionToGeneric_left]
    infer_instance
  have : Flat r := by
    change Flat (restrictionToGeneric j p N j' t hpb e).left
    rw [restrictionToGeneric_left]
    infer_instance
  have hi : Set.range (pullback.fst (N.hom ≫ p) j) =
      N.hom ⁻¹' {(⊥ : PrimeSpectrum R')} := by
    have hgen : p ⁻¹' Set.range j = {(⊥ : PrimeSpectrum R')} :=
      (range_of_isPullback_open hpb.flip).symm.trans (range_specGenericFibreInclusion R' K')
    rw [Scheme.Pullback.range_fst]
    change N.hom ⁻¹' (p ⁻¹' Set.range j) = _
    exact congrArg (Set.preimage (⇑N.hom)) hgen
  obtain ⟨U, hU, hqa, hgen⟩ := exists_invariant_quasiAffine_open d j r
    (neronDescentDatum_compatibleOnOpen j p N j' t hpb e hex) hi
  have : U.toScheme.IsQuasiAffine := hqa
  obtain ⟨V, hV, haf, hsub, _⟩ :=
    d.exists_invariant_affineOpen_between hU (finite_fibreGeneric N.hom) (fun x hx => hgen x hx)
  exact ⟨V, hV, haf, fun x hx => hsub hx⟩

end NeronDVR
