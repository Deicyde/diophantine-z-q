/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New finite-stage shrinking after the ten-file checkpoint. The result
constructs WHOLE special-fibre isomorphism from an actual rational residue
point, and surjectivity/faithful flatness from the local base. It neither
constructs a henselization nor assumes stage/model properness.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.PointedRefinement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.PointedRefinement

/-- A rational point over a closed base point actually refines to an affine
    etale neighbourhood whose whole scheme-theoretic fibre is the residue
    scheme. Thus the old whole-fibre Mono input is an OUTPUT here. -/
theorem exists_affine_refinement_with_isIso_fibre
    {U S : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (c : S) (hc : IsClosed ({c} : Set S))
    (x : Spec (S.residueField c) ⟶ U)
    (hx : x ≫ p = S.fromSpecResidueField c) :
    ∃ V : U.Opens, IsAffineOpen V ∧
      IsIso ((V.ι ≫ p).fiberToSpecResidueField c) ∧
      ∃ x' : Spec (S.residueField c) ⟶ V.toScheme,
        x' ≫ V.ι = x ∧ x' ≫ (V.ι ≫ p) = S.fromSpecResidueField c := by
  let i := S.fromSpecResidueField c
  haveI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hc
  let s : Spec (S.residueField c) ⟶ pullback p i :=
    pullback.lift x (𝟙 _) (by simpa only [Category.id_comp] using hx)
  have hs : s ≫ pullback.snd p i = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨V, hV, e, he, hcomp⟩ := exists_affine_refinement_of_closed_fibre_section p i s hs
  haveI : IsIso (pullback.snd (V.ι ≫ p) i) := by
    rw [← he]
    infer_instance
  let x' : Spec (S.residueField c) ⟶ V.toScheme := e.hom ≫ pullback.fst (V.ι ≫ p) i
  have hx' : x' ≫ V.ι = x := by
    have he' := congrArg (· ≫ pullback.fst p i) hcomp
    change (e.hom ≫ pullback.fst (V.ι ≫ p) i) ≫ V.ι = x
    simpa only [Category.assoc, fibreComparison_fst, s, pullback.lift_fst] using he'
  refine ⟨V, hV, inferInstanceAs (IsIso (pullback.snd (V.ι ≫ p) i)), x', hx', ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← he, e.hom_inv_id, Category.id_comp]

/-- A flat locally finitely presented morphism to a local spectrum is
    surjective once its image contains the local closed point. All points
    specialize to that closed point, and the ACTUAL morphism's image is open. -/
theorem surjective_of_closedPoint_mem_range
    {R : Type u} [CommRing R] [IsLocalRing R] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Flat p] [LocallyOfFinitePresentation p]
    (hc : IsLocalRing.closedPoint R ∈ Set.range p) : Surjective p := by
  have hopen : IsOpen (Set.range p) := by
    simpa only [Set.image_univ] using p.isOpenMap Set.univ isOpen_univ
  constructor
  intro c
  exact (IsLocalRing.specializes_closedPoint c).mem_open hopen hc

/-- The ring map on an affine source, with the original R retained via its
    canonical Γ(Spec R) identification. -/
def affineStructureMap {R : Type u} [CommRing R] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) : R →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop).hom

/-- Faithful flatness of the ACTUAL affine structure map is proved, not
    supplied as an extra descent assumption. -/
theorem affineStructureMap_faithfullyFlat
    {R : Type u} [CommRing R] {U : Scheme.{u}} [IsAffine U]
    (p : U ⟶ Spec (CommRingCat.of R)) [Flat p] [Surjective p] :
    (affineStructureMap p).FaithfullyFlat := by
  have hff : p.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p).mp ⟨inferInstance, inferInstance⟩
  have hΓ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.bijective
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hΓ hff

/-- Full finite-stage refinement over the ORIGINAL local ring. The chosen
    affine neighbourhood is etale, surjective, quasi-compact and genuinely
    faithfully flat, and its entire special fibre is isomorphic to κ(c).
    No model/properness/quotient hypothesis is introduced. -/
theorem exists_affine_etale_faithfullyFlat_refinement
    {R : Type u} [CommRing R] [IsLocalRing R] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Etale p]
    (x : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ U)
    (hx : x ≫ p = (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) :
    ∃ V : U.Opens, IsAffineOpen V ∧ Etale (V.ι ≫ p) ∧ Surjective (V.ι ≫ p) ∧
      QuasiCompact (V.ι ≫ p) ∧ IsIso ((V.ι ≫ p).fiberToSpecResidueField (IsLocalRing.closedPoint R)) ∧
      (affineStructureMap (V.ι ≫ p)).FaithfullyFlat ∧
      ∃ x' : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ V.toScheme,
        x' ≫ V.ι = x ∧
        x' ≫ (V.ι ≫ p) = (Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) := by
  have hc : IsClosed ({IsLocalRing.closedPoint R} : Set (Spec (CommRingCat.of R))) := by
    exact IsLocalRing.isClosed_singleton_closedPoint R
  obtain ⟨V, hV, hIso, x', hinc, hover⟩ :=
    exists_affine_refinement_with_isIso_fibre p (IsLocalRing.closedPoint R) hc x hx
  haveI : IsAffine V.toScheme := hV
  haveI : Etale (V.ι ≫ p) := inferInstance
  have hpoint : IsLocalRing.closedPoint R ∈ Set.range (V.ι ≫ p) := by
    have hc' : IsLocalRing.closedPoint R ∈ Set.range
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) := by
      rw [Scheme.range_fromSpecResidueField]
      exact Set.mem_singleton _
    obtain ⟨t₀, ht₀⟩ := hc'
    refine ⟨x' t₀, ?_⟩
    have he := congrArg
      (fun q : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶ Spec (CommRingCat.of R) => q t₀) hover
    have he' : (V.ι ≫ p) (x' t₀) =
        ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) t₀ := by
      simpa only [Scheme.Hom.comp_apply] using he
    exact he'.trans ht₀
  haveI : Surjective (V.ι ≫ p) := surjective_of_closedPoint_mem_range (V.ι ≫ p) hpoint
  haveI : IsAffineHom (V.ι ≫ p) := inferInstance
  exact ⟨V, hV, inferInstance, inferInstance, inferInstance, hIso,
    affineStructureMap_faithfullyFlat (V.ι ≫ p), x', hinc, hover⟩

#print axioms exists_affine_refinement_with_isIso_fibre
#print axioms affineStructureMap_faithfullyFlat
#print axioms exists_affine_etale_faithfullyFlat_refinement

end ZInQ.Contrib.CloudR2NOS.GoodDescent.PointedRefinement
