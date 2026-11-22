/-
Additive actual κ(R)-pointed étale colimit interface.  Stage maps may be
noninjective; no scheme/model descent, Spec-limit, Mono or special-fibre
IsIso is inferred.  This only exposes the genuine proof-bearing diagram
already contained in indEtale and the actual ordinary residue point.
-/
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.OrdinaryInside

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary

open IsLocalRing CategoryTheory CategoryTheory.Limits
open ZInQ.Contrib.CloudR2Raynaud.StrictHenselization

/-- Bundle the literal ordinary residue point as an R-algebra homomorphism. -/
def residuePointAlgHom
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (e : ResidueField R ≃+* ResidueField S)
    (he : ∀ r : R, e (residue R r) = residue S (algebraMap R S r)) :
    S →ₐ[R] ResidueField R :=
  { toRingHom := residuePoint e
    commutes' := fun r => by
      change e.symm (residue S (algebraMap R S r)) = algebraMap R (ResidueField R) r
      rw [← he r, e.symm_apply_apply, ResidueField.algebraMap_eq] }

/-- ACTUAL filtered diagram/cocone/colimit and compatible κ(R)-rational
    points on every finite étale stage.  No stage inclusion is assumed. -/
theorem exists_pointedEtalePresentation
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (hind : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S))
    (e : ResidueField R ≃+* ResidueField S)
    (he : ∀ r : R, e (residue R r) = residue S (algebraMap R S r)) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J (CommAlgCat.of R S)),
      (∀ j : J, Algebra.Etale R (pres.diag.obj j)) ∧
      ∃ aug : ∀ j : J, pres.diag.obj j →ₐ[R] ResidueField R,
        (∀ j : J, aug j = (residuePointAlgHom e he).comp (pres.ι.app j).hom) ∧
        ∀ {j k : J} (f : j ⟶ k), (aug k).comp (pres.diag.map f).hom = aug j := by
  obtain ⟨J, hcat, hfilter, pres, het⟩ := hind
  letI : SmallCategory J := hcat
  letI : IsFiltered J := hfilter
  let aug : ∀ j : J, pres.diag.obj j →ₐ[R] ResidueField R :=
    fun j => (residuePointAlgHom e he).comp (pres.ι.app j).hom
  refine ⟨J, hcat, hfilter, pres, het, aug, fun _ => rfl, ?_⟩
  intro j k f
  dsimp only [aug]
  rw [AlgHom.comp_assoc]
  have hnat : (pres.ι.app k).hom.comp (pres.diag.map f).hom = (pres.ι.app j).hom :=
    congrArg CommAlgCat.Hom.hom (pres.w f)
  rw [hnat]

/-- The canonical residue-map equivalence is a genuine bijection, not a
    field isomorphism with an unrelated scalar map. -/
theorem residueMap_bijective_of_equiv
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring K) (P : ValuationSubring L)
    (hP : P.comap (algebraMap K L) = O)
    (e : ResidueField O ≃+* ResidueField P) (he : residueMap hP = e.toRingHom) :
    Function.Bijective (residueMap hP) := by
  rw [he]
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using e.bijective

end ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.Ordinary
