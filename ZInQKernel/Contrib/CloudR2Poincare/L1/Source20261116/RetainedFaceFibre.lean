import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.FieldFaceModels
import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceTruncModels
import ZInQKernel.Contrib.CloudR2Poincare.L5.ScalarFibre20261115.RetainedMaps
import ZInQKernel.Contrib.CloudR2Poincare.L3.CechFacePromotion.Int

/-!
# Retained original Čech maps on actual field fibres

Source-only integration. A model comparison is extended FIRST, using the
same stored map and homotopy. Only the canonical ΓSpec restriction is then
commuted with homology. There is no nonflat homology/base-change assumption.
The geometric caller constructs the Čech isomorphisms with the native
base-change maps and L3's literal scalar/face square. No comparison is chosen
from dimensions. The unconditional geometry constructor is in
`ConsumerStatements`; these transport lemmas keep its actual witnesses.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

namespace RetainedFaceFibreConstruction

/-- The original raw extension, with its coefficient map retained. -/
abbrev scalarComplexFunctor {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  (ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)

/-- The only restriction used here is along the actual ΓSpec inverse. -/
abbrev fieldRestrictionComplexFunctor (K : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ ⥤ CochainComplex (ModuleCat.{u} K) ℤ :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).mapHomologicalComplex (.up ℤ)

/-- The actual iterated scalar comparison, not a homology-selected map. -/
def retainedFieldChainMap
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : P ⟶ (scalarComplexFunctor α).obj C)
    (CB : CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ)
    (eB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj C ≅ CB) :
    (scalarComplexFunctor β).obj P ⟶ (fieldRestrictionComplexFunctor K).obj CB :=
  (scalarComplexFunctor β).map e ≫
    (L5.ScalarFibre20261115.gammaScalarCompositeCochainIso α K β).hom.app C ≫
      (fieldRestrictionComplexFunctor K).map eB.hom

/-- Universal quasi-isomorphism witnesses are instantiated using the literal
β.toAlgebra, with no scalar-flatness premise. -/
theorem quasiIso_extended_retained_map
    {A S : Type u} [CommRing A] [CommRing S] (α : A →+* S)
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : P ⟶ (scalarComplexFunctor α).obj C)
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso ((scalarComplexFunctor (algebraMap S B)).map e))
    (K : CommRingCat.{u}) (β : S →+* K) :
    QuasiIso ((scalarComplexFunctor β).map e) := by
  letI : Algebra S K := β.toAlgebra
  exact universal K

/-- Every map after the extended retained comparison is an actual iso. -/
theorem quasiIso_retainedFieldChainMap
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : P ⟶ (scalarComplexFunctor α).obj C)
    (CB : CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ)
    (eB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj C ≅ CB)
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso ((scalarComplexFunctor (algebraMap S B)).map e)) :
    QuasiIso (retainedFieldChainMap α K β C P e CB eB) := by
  haveI : QuasiIso ((scalarComplexFunctor β).map e) :=
    quasiIso_extended_retained_map α C P e universal K β
  dsimp only [retainedFieldChainMap]
  infer_instance

/-- Actual homology comparison: extended SAME e, Γ conversion, geometric
Čech map, then exact restriction/homology comparison. -/
def retainedFieldHomologyIso
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (e : P ⟶ (scalarComplexFunctor α).obj C)
    (CB : CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ)
    (eB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj C ≅ CB)
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso ((scalarComplexFunctor (algebraMap S B)).map e)) (n : ℤ) :
    ((scalarComplexFunctor β).obj P).homology n ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).obj (CB.homology n) := by
  haveI := quasiIso_retainedFieldChainMap α K β C P e CB eB universal
  exact asIso (HomologicalComplex.homologyMap
      (retainedFieldChainMap α K β C P e CB eB) n) ≪≫
    (L5.ScalarFibre20261115.restrictionCochainHomologyIso (Scheme.ΓSpecIso K).inv.hom n).app CB

/-- The diagram used in homotopy transport follows from canonical scalar
naturality and the geometric chain square. Neither is replaced by a rank. -/
theorem scalar_geometric_face_square
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (Φ : C ⟶ D)
    {CB DB : CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ} (ΦB : CB ⟶ DB)
    (eCB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj C ≅ CB)
    (eDB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj D ≅ DB)
    (geometricSquare : eCB.hom ≫ ΦB =
      (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).map Φ ≫ eDB.hom) :
    (scalarComplexFunctor β).map ((scalarComplexFunctor α).map Φ) ≫
        ((L5.ScalarFibre20261115.gammaScalarCompositeCochainIso α K β).hom.app D ≫
          (fieldRestrictionComplexFunctor K).map eDB.hom) =
      ((L5.ScalarFibre20261115.gammaScalarCompositeCochainIso α K β).hom.app C ≫
        (fieldRestrictionComplexFunctor K).map eCB.hom) ≫
          (fieldRestrictionComplexFunctor K).map ΦB := by
  let F := scalarComplexFunctor β
  let E := scalarComplexFunctor α
  let G := scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))
  let R := fieldRestrictionComplexFunctor K
  let δ := L5.ScalarFibre20261115.gammaScalarCompositeCochainIso α K β
  have hn : F.map (E.map Φ) ≫ δ.hom.app D = δ.hom.app C ≫ R.map (G.map Φ) :=
    L5.ScalarFibre20261115.gammaScalarCompositeCochainIso_naturality α K β C D Φ
  have hg : R.map eCB.hom ≫ R.map ΦB = R.map (G.map Φ) ≫ R.map eDB.hom := by
    rw [← R.map_comp, geometricSquare, R.map_comp]
  calc
    _ = (F.map (E.map Φ) ≫ δ.hom.app D) ≫ R.map eDB.hom := (Category.assoc _ _ _).symm
    _ = (δ.hom.app C ≫ R.map (G.map Φ)) ≫ R.map eDB.hom := by rw [hn]
    _ = δ.hom.app C ≫ (R.map (G.map Φ) ≫ R.map eDB.hom) := Category.assoc _ _ _
    _ = δ.hom.app C ≫ (R.map eCB.hom ≫ R.map ΦB) := by rw [← hg]
    _ = _ := (Category.assoc _ _ _).symm

/-- Transport the SAME actual stored homotopy through scalar extension and
canonical Čech comparison. All scalars are allowed, including residue fields. -/
def retainedFieldFaceHomotopy
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (Φ : C ⟶ D)
    {P PX : CochainComplex (ModuleCat.{u} S) ℤ} (ψ : P ⟶ PX)
    (eC : P ⟶ (scalarComplexFunctor α).obj C)
    (eX : PX ⟶ (scalarComplexFunctor α).obj D)
    (h : Homotopy (ψ ≫ eX) (eC ≫ (scalarComplexFunctor α).map Φ))
    {CB DB : CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ} (ΦB : CB ⟶ DB)
    (eCB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj C ≅ CB)
    (eDB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj D ≅ DB)
    (geometricSquare : eCB.hom ≫ ΦB =
      (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).map Φ ≫ eDB.hom) :
    Homotopy ((scalarComplexFunctor β).map ψ ≫
        retainedFieldChainMap α K β D PX eX DB eDB)
      (retainedFieldChainMap α K β C P eC CB eCB ≫
        (fieldRestrictionComplexFunctor K).map ΦB) := by
  let R := fieldRestrictionComplexFunctor K
  let δ := L5.ScalarFibre20261115.gammaScalarCompositeCochainIso α K β
  let iC := δ.hom.app C ≫ R.map eCB.hom
  let iD := δ.hom.app D ≫ R.map eDB.hom
  letI : Algebra S K := β.toAlgebra
  have hβ : Homotopy ((scalarComplexFunctor β).map ψ ≫ (scalarComplexFunctor β).map eX)
      ((scalarComplexFunctor β).map eC ≫ (scalarComplexFunctor β).map ((scalarComplexFunctor α).map Φ)) :=
    scalarExtension_faceSquare_homotopy K h
  exact retainedFaceHomotopy_postcompose iC iD (R.map ΦB)
    (scalar_geometric_face_square α K β Φ ΦB eCB eDB geometricSquare) hβ

/-- Homology of the actual retained homotopy gives the original field-linear
face square. Restriction is applied only after raw extension. -/
theorem retainedFieldHomologyIso_face_square
    {A S : Type u} [CommRing A] [CommRing S]
    (α : A →+* S) (K : CommRingCat.{u}) (β : S →+* K)
    {C D : CochainComplex (ModuleCat.{u} A) ℤ} (Φ : C ⟶ D)
    {P PX : CochainComplex (ModuleCat.{u} S) ℤ} (ψ : P ⟶ PX)
    (eC : P ⟶ (scalarComplexFunctor α).obj C)
    (eX : PX ⟶ (scalarComplexFunctor α).obj D)
    (h : Homotopy (ψ ≫ eX) (eC ≫ (scalarComplexFunctor α).map Φ))
    (uC : ∀ (B : Type u) [CommRing B] [Algebra S B], QuasiIso ((scalarComplexFunctor (algebraMap S B)).map eC))
    (uX : ∀ (B : Type u) [CommRing B] [Algebra S B], QuasiIso ((scalarComplexFunctor (algebraMap S B)).map eX))
    {CB DB : CochainComplex (ModuleCat.{u} Γ(Spec K, ⊤)) ℤ} (ΦB : CB ⟶ DB)
    (eCB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj C ≅ CB)
    (eDB : (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).obj D ≅ DB)
    (geometricSquare : eCB.hom ≫ ΦB =
      (scalarComplexFunctor ((Scheme.ΓSpecIso K).inv.hom.comp (β.comp α))).map Φ ≫ eDB.hom) (n : ℤ) :
    HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) n ≫
        (retainedFieldHomologyIso α K β D PX eX DB eDB uX n).hom =
      (retainedFieldHomologyIso α K β C P eC CB eCB uC n).hom ≫
        (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).map
          (HomologicalComplex.homologyMap ΦB n) := by
  let R := fieldRestrictionComplexFunctor K
  let σ := L5.ScalarFibre20261115.restrictionCochainHomologyIso (Scheme.ΓSpecIso K).inv.hom n
  let aC := retainedFieldChainMap α K β C P eC CB eCB
  let aX := retainedFieldChainMap α K β D PX eX DB eDB
  have hH : HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) n ≫
      HomologicalComplex.homologyMap aX n =
      HomologicalComplex.homologyMap aC n ≫ HomologicalComplex.homologyMap (R.map ΦB) n := by
    have hh := (retainedFieldFaceHomotopy α K β Φ ψ eC eX h ΦB eCB eDB geometricSquare).homologyMap_eq n
    simpa only [HomologicalComplex.homologyMap_comp] using hh
  have hσ : HomologicalComplex.homologyMap (R.map ΦB) n ≫ (σ.app DB).hom =
      (σ.app CB).hom ≫ (ModuleCat.restrictScalars (Scheme.ΓSpecIso K).inv.hom).map
        (HomologicalComplex.homologyMap ΦB n) := σ.hom.naturality ΦB
  change HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) n ≫
      (HomologicalComplex.homologyMap aX n ≫ (σ.app DB).hom) =
    (HomologicalComplex.homologyMap aC n ≫ (σ.app CB).hom) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ (σ.app DB).hom) hH).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun y => HomologicalComplex.homologyMap aC n ≫ y) hσ).trans
          (Category.assoc _ _ _).symm)))

end RetainedFaceFibreConstruction

end ZInQ.Contrib.CloudR2Poincare.L1
