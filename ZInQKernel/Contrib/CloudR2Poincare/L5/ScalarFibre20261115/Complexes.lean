import ZInQKernel.Contrib.CloudR2Poincare.L5.ScalarFibre20261115.Coefficients
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Integer-complex and all-degree homology scalar-fibre conversion

Only scalar restriction along the ACTUAL Gamma-Spec isomorphism is commuted
with homology. Beta extension is done FIRST; it is not assumed flat/exact.
The functor iso is coefficient-natural for every actual morphism, so the SAME
retained model/face maps survive conversion. Integer complexes and their full
mapping cones, including degree -1, are retained without truncation.

L2's independent raw-tilde/cone fibre comparison is reused, not reproved here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry HomologicalComplex

namespace ZInQ.Contrib.CloudR2Poincare.L5.ScalarFibre20261115

/-- The canonical scalar functor conversion prolonged to ACTUAL integer
complexes, retaining the original module and every differential. -/
def gammaScalarCochainIso {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) :
    (ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (gammaScalarExtensionIso K β) (.up ℤ)

/-- Literal component lock: each degree is the original coefficient iso. -/
theorem gammaScalarCochainIso_f {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) (P : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    ((gammaScalarCochainIso K β).hom.app P).f n =
      (gammaScalarExtensionIso K β).hom.app (P.X n) := rfl

/-- The original chain map Phi is preserved by the actual natural iso. -/
theorem gammaScalarCochainIso_naturality {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K)
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) :
    ((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).map Φ ≫
        (gammaScalarCochainIso K β).hom.app D =
      (gammaScalarCochainIso K β).hom.app P ≫
        ((ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)).map
          (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
            (.up ℤ)).map Φ) :=
  (gammaScalarCochainIso K β).hom.naturality Φ

/-- Exact scalar RESTRICTION commutes with homology. This says NOTHING about
commuting possibly nonflat beta extension with homology. -/
def restrictionCochainHomologyIso {K G : Type u} [CommRing K] [CommRing G]
    (η : K →+* G) (q : ℤ) :
    (ModuleCat.restrictScalars η).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (.up ℤ) q ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} G) (.up ℤ) q ⋙
        ModuleCat.restrictScalars η :=
  NatIso.ofComponents
    (fun P => (P.sc q).mapHomologyIso (ModuleCat.restrictScalars η))
    (fun Φ => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} G) (.up ℤ) q).map Φ)
      (ModuleCat.restrictScalars η))

/-- Actual K-module homology conversion, NATURAL in every original complex
and map, at EVERY integer q (including negative degrees). -/
def gammaScalarHomologyNatIso {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) (q : ℤ) :
    (ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (.up ℤ) q ≅
      ((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(Spec K, ⊤)) (.up ℤ) q) ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom := by
  let E := (ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex (.up ℤ)
  let R := (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (.up ℤ) q
  let HG := HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(Spec K, ⊤)) (.up ℤ) q
  let RS := ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom
  exact Functor.isoWhiskerRight (gammaScalarCochainIso K β) H ≪≫
    Functor.associator E R H ≪≫
      Functor.isoWhiskerLeft E (restrictionCochainHomologyIso (Scheme.ΓSpecIso K).inv.hom q) ≪≫
        (Functor.associator E HG RS).symm

/-- The requested actual original-K-linear all-degree homology isomorphism. -/
def gammaScalarHomologyIso {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K) (P : CochainComplex (ModuleCat.{u} S) ℤ) (q : ℤ) :
    (((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).obj P).homology q ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).obj
        ((((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
          (.up ℤ)).obj P).homology q) :=
  (gammaScalarHomologyNatIso K β q).app P

/-- Homology naturality on the SAME actual Phi, not a rank-selected map. -/
theorem gammaScalarHomologyIso_naturality {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K)
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (q : ℤ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).map Φ) q ≫
      (gammaScalarHomologyIso K β D q).hom =
    (gammaScalarHomologyIso K β P q).hom ≫
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).map
        (HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
            (.up ℤ)).map Φ) q) :=
  (gammaScalarHomologyNatIso K β q).hom.naturality Φ

/-- The ACTUAL full mapping cones are converted without assuming beta-flatness
or killing the degree -1 term. This is induced by actual additive cone maps. -/
def gammaScalarConeHomologyIso {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K)
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (q : ℤ) :
    (CochainComplex.mappingCone
      (((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).map Φ)).homology q ≅
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).obj
      ((CochainComplex.mappingCone
        (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
          (.up ℤ)).map Φ)).homology q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (.up ℤ) q).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso Φ (ModuleCat.extendScalars β)).symm ≪≫
    gammaScalarHomologyIso K β (CochainComplex.mappingCone Φ) q ≪≫
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapIso
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(Spec K, ⊤)) (.up ℤ) q).mapIso
          (CochainComplex.mappingCone.mapHomologicalComplexIso Φ
            (ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β))))

/-- Exact degree-minus-one cone consumer, no truncation or vanishing assertion. -/
def gammaScalarConeHomologyIso_negOne {S : Type u} [CommRing S]
    (K : CommRingCat.{u}) (β : S →+* K)
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) :
    (CochainComplex.mappingCone
      (((ModuleCat.extendScalars β).mapHomologicalComplex (.up ℤ)).map Φ)).homology (-1) ≅
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).obj
      ((CochainComplex.mappingCone
        (((ModuleCat.extendScalars ((Scheme.ΓSpecIso K).inv.hom.comp β)).mapHomologicalComplex
          (.up ℤ)).map Φ)).homology (-1)) :=
  gammaScalarConeHomologyIso K β P D Φ (-1)

/-- Residue-specialized integer-complex conversion, reusing L2 beta and ONLY
the proved Gamma ring triangle. -/
def residueGammaScalarCochainIso (S : Type u) [CommRing S] (s : Spec (.of S)) :
    (ModuleCat.extendScalars (L2.nativeResidueScalarMap S s)).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars
        ((Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop).hom).mapHomologicalComplex
          (.up ℤ) ⋙
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).inv.hom).mapHomologicalComplex
          (.up ℤ) :=
  NatIso.mapHomologicalComplex (residueGammaScalarExtensionIso S s) (.up ℤ)

end ZInQ.Contrib.CloudR2Poincare.L5.ScalarFibre20261115
