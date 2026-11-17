import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeCohomologyLocus
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackTilde
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Field
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Canonical raw-ring cone / tilde / residue-field homology comparisons

The scalar map is the ORIGINAL residue morphism, expressed through native
Gamma-Spec. All native CommRingCat dictionaries are retained, including the
actual residue-field object. Native tilde pullback commutes with ORIGINAL
scalar extension; canonical additive-functor cone maps identify actual cones.
Over the actual field, tilde/global-sections preserve homology by the native
field equivalence. No residue-flatness, nonnegative cone, rank-selected
comparison or supplied model geometry is assumed. L1's semantic Cech face
squares remain separate and unchanged.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry HomologicalComplex

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- The ORIGINAL residue map expressed as a native ring-category arrow;
the actual residue-field ring object/dictionary is not reconstructed. -/
def nativeResidueRingMap (S : Type u) [CommRing S] (s : Spec (.of S)) :
    CommRingCat.of S ⟶ (Spec (.of S)).residueField s :=
  (Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop ≫
    (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).hom

/-- Literal raw S -> kappa(s) scalar map for L1's ALL-S-algebras witnesses. -/
def nativeResidueScalarMap (S : Type u) [CommRing S] (s : Spec (.of S)) :
    S →+* (Spec (.of S)).residueField s := (nativeResidueRingMap S s).hom

/-- Exact Gamma-Spec formula, with the ORIGINAL residue point and dictionary. -/
theorem nativeResidueScalarMap_eq_gamma (S : Type u) [CommRing S] (s : Spec (.of S)) :
    nativeResidueScalarMap S s =
      ((Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).hom).hom := rfl

/-- The Gamma map is exactly the preimage of the ORIGINAL scheme point,
not an arbitrary field isomorphism or numerical comparison. -/
theorem nativeResidueRingMap_eq_preimage (S : Type u) [CommRing S] (s : Spec (.of S)) :
    nativeResidueRingMap S s = Spec.preimage ((Spec (.of S)).fromSpecResidueField s) := by
  let ρ := Spec.preimage ((Spec (.of S)).fromSpecResidueField s)
  have h := Scheme.ΓSpecIso_inv_naturality ρ
  rw [Spec.map_preimage] at h
  change (Scheme.ΓSpecIso (.of S)).inv ≫ ((Spec (.of S)).fromSpecResidueField s).appTop ≫
    (Scheme.ΓSpecIso ((Spec (.of S)).residueField s)).hom = ρ
  rw [← Category.assoc, ← h]
  simp

/-- Spec(beta_s) is the ACTUAL residue-field morphism, using its native arrow. -/
theorem nativeResidueScalarMap_specMap (S : Type u) [CommRing S] (s : Spec (.of S)) :
    Spec.map (nativeResidueRingMap S s) = (Spec (.of S)).fromSpecResidueField s := by
  rw [nativeResidueRingMap_eq_preimage, Spec.map_preimage]

/-- beta_s.toAlgebra gives literally beta_s as algebraMap. It is not a global
instance or a substituted scalar map. -/
theorem nativeResidueScalarMap_algebraMap (S : Type u) [CommRing S] (s : Spec (.of S)) :
    letI : Algebra S ((Spec (.of S)).residueField s) := (nativeResidueScalarMap S s).toAlgebra
    algebraMap S ((Spec (.of S)).residueField s) = nativeResidueScalarMap S s := rfl

/-- Native tilde is additive. This explicitly uses its original adjunction
and preserves the CURRENT native category dictionaries; local registration only. -/
theorem nativeTildeFunctor_additive (R : CommRingCat.{u}) : (tilde.functor R).Additive := by
  letI : (tilde.functor R).IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor R)
  exact Functor.additive_of_preservesBinaryBiproducts (tilde.functor R)

attribute [local instance] nativeTildeFunctor_additive

/-- Native tilde prolonged to integer complexes, retaining the actual ring object. -/
def nativeTildeCochainFunctor (R : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (Spec R).Modules ℤ :=
  (tilde.functor R).mapHomologicalComplex (.up ℤ)

/-- ORIGINAL scalar-extension complexes along beta_s, with actual residue ring. -/
def nativeResidueCochainFunctor (S : Type u) [CommRing S] (s : Spec (.of S)) :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤
      CochainComplex (ModuleCat.{u} ((Spec (.of S)).residueField s)) ℤ :=
  (ModuleCat.extendScalars (nativeResidueScalarMap S s)).mapHomologicalComplex (.up ℤ)

/-- Canonical additive-functor cone comparison for ORIGINAL raw tilde. -/
def nativeTildeMappingConeIso (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) :
    (nativeTildeCochainFunctor (.of S)).obj (CochainComplex.mappingCone Φ) ≅
      CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ) := by
  let H : ModuleCat.{u} S ⥤ (Spec (.of S)).Modules := tilde.functor (.of S)
  letI : H.Additive := nativeTildeFunctor_additive (.of S)
  exact CochainComplex.mappingCone.mapHomologicalComplexIso Φ H

/-- The ACTUAL cone comparison respects the ACTUAL right inclusion. -/
theorem nativeTildeMappingConeIso_inr (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) :
    (nativeTildeCochainFunctor (.of S)).map (CochainComplex.mappingCone.inr Φ) ≫
      (nativeTildeMappingConeIso S P D Φ).hom =
    CochainComplex.mappingCone.inr ((nativeTildeCochainFunctor (.of S)).map Φ) := by
  let H : ModuleCat.{u} S ⥤ (Spec (.of S)).Modules := tilde.functor (.of S)
  letI : H.Additive := nativeTildeFunctor_additive (.of S)
  exact CochainComplex.mappingCone.map_inr Φ H

/-- Canonical additive-functor cone comparison for ORIGINAL beta_s extension,
with no flatness or bounds on complexes. -/
def nativeResidueMappingConeIso (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (s : Spec (.of S)) :
    (nativeResidueCochainFunctor S s).obj (CochainComplex.mappingCone Φ) ≅
      CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso Φ
    (ModuleCat.extendScalars (nativeResidueScalarMap S s))

/-- Native affine tilde pullback comparison on ACTUAL integer complexes,
for ANY native ring map, without flatness. -/
def nativeScalarTildeComplexIso {R B : CommRingCat.{u}} (β : R ⟶ B)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((Scheme.Modules.pullback (Spec.map β)).mapHomologicalComplex (.up ℤ)).obj
      ((nativeTildeCochainFunctor R).obj P)) ≅
    ((nativeTildeCochainFunctor B).obj
      (((ModuleCat.extendScalars β.hom).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (NatIso.mapHomologicalComplex (Scheme.Modules.tildePullbackIso β) (.up ℤ)).app P

/-- The complex comparison has precisely the ACTUAL native tildePullbackIso components. -/
theorem nativeScalarTildeComplexIso_f {R B : CommRingCat.{u}} (β : R ⟶ B)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (nativeScalarTildeComplexIso β P).hom.f n =
      (Scheme.Modules.tildePullbackIso β).hom.app (P.X n) := rfl

/-- Ordinary native naturality for the ORIGINAL scalar/tilde chain map;
this is not the separate semantic Cech/H face square. -/
theorem nativeScalarTildeComplexIso_naturality {R B : CommRingCat.{u}} (β : R ⟶ B)
    (P D : CochainComplex (ModuleCat.{u} R) ℤ) (Φ : P ⟶ D) :
    ((Scheme.Modules.pullback (Spec.map β)).mapHomologicalComplex (.up ℤ)).map
        ((nativeTildeCochainFunctor R).map Φ) ≫ (nativeScalarTildeComplexIso β D).hom =
      (nativeScalarTildeComplexIso β P).hom ≫ (nativeTildeCochainFunctor B).map
        (((ModuleCat.extendScalars β.hom).mapHomologicalComplex (.up ℤ)).map Φ) :=
  (NatIso.mapHomologicalComplex (Scheme.Modules.tildePullbackIso β) (.up ℤ)).hom.naturality Φ

/-- ORIGINAL residue pullback of ORIGINAL tilde is ORIGINAL beta_s extension
followed by tilde over the original residue-field object. -/
def nativeResidueTildeComplexIso (S : Type u) [CommRing S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) (s : Spec (.of S)) :
    (((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex (.up ℤ)).obj
      ((nativeTildeCochainFunctor (.of S)).obj P)) ≅
    ((nativeTildeCochainFunctor ((Spec (.of S)).residueField s)).obj
      ((nativeResidueCochainFunctor S s).obj P)) :=
  ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackCongr
      (nativeResidueScalarMap_specMap S s)).symm (.up ℤ)).app
      ((nativeTildeCochainFunctor (.of S)).obj P)) ≪≫
    nativeScalarTildeComplexIso (nativeResidueRingMap S s) P

/-- Canonical tilde/global-sections homology comparison over an ACTUAL field
object. No field/rank isomorphism is selected and no dimension input is used. -/
def nativeFieldTildeHomologyIso (K : CommRingCat.{u}) (hK : IsField K)
    (P : CochainComplex (ModuleCat.{u} K) ℤ) (q : ℤ) :
    P.homology q ≅ (moduleSpecΓFunctor (R := K)).obj
      (((nativeTildeCochainFunctor K).obj P).homology q) := by
  letI : (moduleSpecΓFunctor (R := K)).IsEquivalence := isEquivalence_moduleSpecΓFunctor hK
  letI : (tilde.functor K).IsEquivalence :=
    (tilde.adjunction (R := K)).isEquivalence_left_of_isEquivalence_right
  let e : (((nativeTildeCochainFunctor K).obj P).homology q) ≅ (tilde.functor K).obj (P.homology q) := by
    exact (P.sc q).mapHomologyIso (tilde.functor K)
  exact (tilde.toTildeΓNatIso (R := K)).app (P.homology q) ≪≫
    (moduleSpecΓFunctor (R := K)).mapIso e.symm

/-- ACTUAL scalar-extension cone, sheafified over kappa(s), is ORIGINAL
residue pullback of ACTUAL tilde cone. Both retain degree -1. -/
def nativeResidueTildeConeIso (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (s : Spec (.of S)) :
    ((nativeTildeCochainFunctor ((Spec (.of S)).residueField s)).obj
      (CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ))) ≅
    (((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ))) :=
  (nativeTildeCochainFunctor ((Spec (.of S)).residueField s)).mapIso
      (nativeResidueMappingConeIso S P D Φ s).symm ≪≫
    (nativeResidueTildeComplexIso S (CochainComplex.mappingCone Φ) s).symm ≪≫
    ((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex (.up ℤ)).mapIso
      (nativeTildeMappingConeIso S P D Φ)

/-- AGREED actual canonical kappa(s)-linear homology isomorphism, at ANY
integer degree, with no flat/nonnegative/finite/rank/model hypothesis. -/
def nativeTildeCone_fibreHomologyIso (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (s : Spec (.of S)) (q : ℤ) :
    (CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ)).homology q ≅
      (moduleSpecΓFunctor (R := (Spec (.of S)).residueField s)).obj
        ((((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ))).homology q) :=
  nativeFieldTildeHomologyIso ((Spec (.of S)).residueField s)
      (Field.toIsField ((Spec (.of S)).residueField s))
      (CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ)) q ≪≫
    (moduleSpecΓFunctor (R := (Spec (.of S)).residueField s)).mapIso
      ((HomologicalComplex.homologyFunctor ((Spec ((Spec (.of S)).residueField s)).Modules) (.up ℤ) q).mapIso
        (nativeResidueTildeConeIso S P D Φ s))

/-- Actual arbitrary-degree field finrank equals the UNCHANGED L1 dimension. -/
theorem nativeTildeCone_finrank_eq_derivedFiberDimension (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (s : Spec (.of S)) (q : ℤ) :
    Module.finrank ((Spec (.of S)).residueField s)
      ((CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ)).homology q) =
    L1.derivedFiberDimension (CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ)) q s :=
  (nativeTildeCone_fibreHomologyIso S P D Φ s q).toLinearEquiv.finrank_eq

/-- EXACT preferred H0 consumer; ORIGINAL complexes/maps/scalars are retained. -/
theorem nativeTildeCone_finrankHZero_eq_derivedFiberDimension (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D) (s : Spec (.of S)) :
    Module.finrank ((Spec (.of S)).residueField s)
      ((CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ)).homology 0) =
    L1.derivedFiberDimension (CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ)) 0 s :=
  nativeTildeCone_finrank_eq_derivedFiberDimension S P D Φ s 0

end ZInQ.Contrib.CloudR2Poincare.L2
