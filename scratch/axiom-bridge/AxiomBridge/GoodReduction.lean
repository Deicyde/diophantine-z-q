import AxiomBridge.AbelianVariety
import Mordell.AbelianVariety.GoodReduction

/-! Faltings' flat, finitely presented model with geometrically integral group
fibres is already a PkgI2 abelian scheme. Smoothness follows fibrewise from
Mathlib's smooth group-scheme theorem, then from its flat smooth-fibre criterion.
The prime's valuation subring is identified with the localization inside k.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AxiomBridge

/-- Geometric integrality implies geometric connectedness over any base. -/
theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}}
    (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f :=
  ⟨fun _ _ y Z fst snd h ↦ @IrreducibleSpace.connectedSpace Z _
    ((inferInstance : GeometricallyIrreducible f).geometrically_irreducibleSpace
      y fst snd h)⟩

/-- Faltings' fibre conditions imply the PkgI2 abelian-scheme conditions. -/
theorem pkgI2_isAbelianScheme_of_fibres {O : Type u} [CommRing O]
    (G : Grp (Over (Spec (.of O))))
    (hF : Flat G.X.hom) (hP : IsProper G.X.hom)
    (hL : LocallyOfFinitePresentation G.X.hom)
    (hfib : ∀ w,
      IsProper ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj G.X).hom ∧
      GeometricallyIntegral
        ((Over.pullback (Scheme.fromSpecResidueField _ w)).obj G.X).hom) :
    PkgI2.IsAbelianScheme G := by
  let : Flat G.X.hom := hF
  let : IsProper G.X.hom := hP
  let : LocallyOfFinitePresentation G.X.hom := hL
  let : GrpObj (Over.mk G.X.hom) := G.grp
  let : GeometricallyIntegral G.X.hom :=
    (GeometricallyIntegral.iff_geometricallyIntegral_fiber G.X.hom).2
      fun w ↦ (hfib w).2
  refine ⟨hP, ?_, geometricallyConnected_of_geometricallyIntegral G.X.hom⟩
  refine Smooth.of_smooth_fiberToSpecResidueField G.X.hom fun w ↦ ?_
  let : GeometricallyIntegral (G.X.hom.fiberToSpecResidueField w) := (hfib w).2
  -- Supply finite type explicitly at the residue-field/CommRingCat boundary.
  exact @smooth_of_grpObj ((Spec (.of O)).residueField w) _ _
    (G.X.hom.fiberToSpecResidueField w) (hfib w).1.toLocallyOfFiniteType
    Over.grpObjMkPullbackSnd inferInstance

/-- Axiom's good reduction at a height-one prime implies PkgI2 good reduction
at its canonical adic valuation subring, with the same model and group isomorphism. -/
theorem pkgI2_hasGoodReduction_of_faltings
    (k : Type u) [Field k] [NumberField k]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
    [GeometricallyIntegral A.hom]
    (h : Faltings.HasGoodReduction k p A) :
    PkgI2.HasGoodReduction (Grp.mk A) (p.valuation k).valuationSubring := by
  rw [← p.valuationSubringAtPrime_eq_valuationSubring (K := k)]
  change ∃ G : Grp (Over (Spec (.of
      (Localization.subalgebra.ofField k p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors)))),
    PkgI2.IsAbelianScheme G ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap
        (Localization.subalgebra.ofField k p.asIdeal.primeCompl
          p.asIdeal.primeCompl_le_nonZeroDivisors) k)))).mapGrp.obj G ≅ Grp.mk A)
  rw [Localization.subalgebra.ofField_eq]
  obtain ⟨G, hF, hP, hL, hfib, he⟩ := h
  exact ⟨G, pkgI2_isAbelianScheme_of_fibres G hF hP hL hfib, he⟩

end AxiomBridge

#print axioms AxiomBridge.geometricallyConnected_of_geometricallyIntegral
#print axioms AxiomBridge.pkgI2_isAbelianScheme_of_fibres
#print axioms AxiomBridge.pkgI2_hasGoodReduction_of_faltings
