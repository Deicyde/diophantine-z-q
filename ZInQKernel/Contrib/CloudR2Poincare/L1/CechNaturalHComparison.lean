import ZInQKernel.Contrib.CloudR2Poincare.L1.CechCoefficientMaps
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray

/-!
# Coefficient-natural native Čech/H comparisons

The comparison is built from the literal explicit-complex identity and ONE
native coefficient-natural Čech-to-H comparison, not selected from dimensions.
Its coefficient naturality is retained for constructing the actual face
pullback squares via the actual pushforward coefficient adjunction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The literal abelian-homology comparison respects actual coefficient maps. -/
theorem cechModuleNatHomologyAbIso_naturality
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap (cechModuleCoefficientMapNat q φ U) n) ≫
      (cechModuleNatHomologyAbIso q N U n).hom =
    (cechModuleNatHomologyAbIso q M U n).hom ≫ HomologicalComplex.homologyMap
      ((TopCat.Presheaf.cechComplex U).map ((Scheme.Modules.toPresheaf X).map φ)) n := by
  let F := forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cechModuleCoefficientMapNat q φ U)) F
  have h₂ := congrArg (fun f ↦ HomologicalComplex.homologyMap f n)
    (cechModuleNatForgetAbIso_naturality q φ U)
  simp only [HomologicalComplex.homologyMap_comp] at h₂
  dsimp only [cechModuleNatHomologyAbIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom]
  rw [Category.assoc]
  erw [reassoc_of% h]
  exact congrArg _ h₂

/-- The SAME native natural Čech-to-H comparison for all acyclic coefficients
on the ambient scheme. Proper/separated-family affine intersections provide
its hypotheses; no rank-selected isomorphism is used. -/
def nativeCechHNaturalIso
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ) :
    (Scheme.Modules.cechAcyclicOnAffines X).ι ⋙ TopCat.Sheaf.cechCohomologyFunctor U n ≅
      (Scheme.Modules.cechAcyclicOnAffines X).ι ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology X) n := by
  classical
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from q]
    infer_instance
  have affineInter (k : ℕ) (t : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (t l)) := by
    simpa using (IsAffineOpen.biInf (Set.univ : Set (Fin (k + 1))) Set.finite_univ
      Set.univ_nonempty (fun l _ ↦ affineU (t l)))
  exact (TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH U coverU
    (Scheme.Modules.cechAcyclicOnAffines X)
    (fun _ h ↦ Scheme.Modules.cechAcyclicOnAffines_under_cokernel h)
    (fun _ hS h k t ↦ Scheme.Modules.surjective_app_of_cechAcyclicOnAffines hS h (affineInter k t)) n).some

/-- The actual underlying acyclic coefficient object of a native QC module. -/
def nativeCechHCoefficientObject {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.cechAcyclicOnAffines X).FullSubcategory :=
  ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj M,
    Scheme.Modules.cechAcyclicOnAffines_of_isQuasicoherent M⟩

/-- The actual module-valued Nat Čech comparison, with the retained native
coefficient-natural isomorphism rather than an objectwise dimension choice. -/
def nativeCechHComparisonNat
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ) :
    (Scheme.Modules.cechModuleComplexNat q M U).homology n ≃+ M.H n :=
  (cechModuleNatHomologyAbIso q M U n).addCommGroupIsoToAddEquiv.trans
    ((nativeCechHNaturalIso q U affineU coverU n).app (nativeCechHCoefficientObject M)).addCommGroupIsoToAddEquiv

/-- The ORIGINAL integer Čech comparison. -/
def nativeCechHComparison
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ) :
    (Scheme.Modules.cechModuleComplex q M U).homology n ≃+ M.H n :=
  ((Scheme.Modules.cechModuleComplexNat q M U).extendHomologyIso ComplexShape.embeddingUpNat rfl).toLinearEquiv.toAddEquiv.trans
    (nativeCechHComparisonNat q M U affineU coverU n)

/-- Coefficient naturality for the SAME actual native Čech-to-H comparison. -/
theorem nativeCechHComparisonNat_coefficient_naturality
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (z : (Scheme.Modules.cechModuleComplexNat q M U).homology n) :
    nativeCechHComparisonNat q N U affineU coverU n
        (HomologicalComplex.homologyMap (cechModuleCoefficientMapNat q φ U) n z) =
      Scheme.Modules.H.map φ n (nativeCechHComparisonNat q M U affineU coverU n z) := by
  let eM := cechModuleNatHomologyAbIso q M U n
  let eN := cechModuleNatHomologyAbIso q N U n
  let e := nativeCechHNaturalIso q U affineU coverU n
  let f : nativeCechHCoefficientObject M ⟶ nativeCechHCoefficientObject N :=
    ObjectProperty.homMk ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)
  have h₁ := ConcreteCategory.congr_hom (cechModuleNatHomologyAbIso_naturality q φ U n) z
  simp only [ConcreteCategory.comp_apply] at h₁
  have h₂ := NatTrans.naturality_apply e.hom f (eM.hom z)
  change eN.hom (HomologicalComplex.homologyMap (cechModuleCoefficientMapNat q φ U) n z) = _ at h₁
  change e.hom.app (nativeCechHCoefficientObject N)
      (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        ((Scheme.Modules.toPresheaf X).map φ)) n (eM.hom z)) = _ at h₂
  change e.hom.app (nativeCechHCoefficientObject N)
      (eN.hom (HomologicalComplex.homologyMap (cechModuleCoefficientMapNat q φ U) n z)) = _
  rw [h₁]
  exact h₂

end ZInQ.Contrib.CloudR2Poincare.L1
