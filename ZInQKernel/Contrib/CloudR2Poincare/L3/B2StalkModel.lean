import ZInQKernel.Contrib.CloudR2Poincare.L3.B2SplitComplex
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.StalkPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Exactness

/-!
# Actual stalk-complex contraction and arbitrary pullback

An acyclic bounded-above locally free SHEAF complex has an acyclic bounded
free module complex at each actual stalk. Its actual pullback stalk is the
extension of scalars of that complex, through the native natural tensor/stalk
comparison. Contraction, not flatness of the base change, gives exactness.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The native stalk as a module over the ACTUAL scheme local ring. -/
def stalkModulesFunctor {Y : Scheme.{u}} (y : Y) :
    Y.Modules ⥤ ModuleCat.{u} (Y.presheaf.stalk y) where
  obj F := ModuleCat.of (Y.presheaf.stalk y) (F.presheaf.stalk y)
  map f := ModuleCat.ofHom (f.stalkLinearMap y)
  map_id F := by
    ext a
    change ((Scheme.Modules.stalkFunctor y).map (𝟙 F)) a = a
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    ext a
    change ((Scheme.Modules.stalkFunctor y).map (f ≫ g)) a =
      ((Scheme.Modules.stalkFunctor y).map g) (((Scheme.Modules.stalkFunctor y).map f) a)
    rw [CategoryTheory.Functor.map_comp]
    rfl

local instance stalkModulesFunctor_additive {Y : Scheme.{u}} (y : Y) :
    (stalkModulesFunctor y).Additive where
  map_add := by
    intro F G f g
    ext a
    change ((Scheme.Modules.stalkFunctor y).map (f + g)) a =
      ((Scheme.Modules.stalkFunctor y).map f) a + ((Scheme.Modules.stalkFunctor y).map g) a
    rw [CategoryTheory.Functor.map_add]
    rfl

/-- Exactness of the actual module stalk complex, reflected through its native
underlying abelian stalk complex. -/
theorem acyclic_stalkModulesFunctor_of_acyclic {Y : Scheme.{u}}
    (P : CochainComplex Y.Modules ℤ) (hP : P.Acyclic) (y : Y) :
    (((stalkModulesFunctor y).mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  intro q
  rw [HomologicalComplex.exactAt_iff]
  apply (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (ModuleCat (Y.presheaf.stalk y)) AddCommGrpCat)).mp
  exact (HomologicalComplex.exactAt_iff _ q).mp
    ((Scheme.Modules.exactAt_iff_stalkFunctor P q).mp (hP q) y)

/-- The actual stalk module of a locally free native coefficient is free. -/
theorem free_stalkModulesFunctor_of_locallyFree {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsLocallyFree] (y : Y) :
    Module.Free (Y.presheaf.stalk y) ((stalkModulesFunctor y).obj F) :=
  StacksPort.Stacks.StalkFreeBridge.free_stalk_of_isLocallyFree F y

/-- Arbitrary pullback of an acyclic bounded-above locally free sheaf complex
is acyclic, through actual stalk module complexes and their native comparison. -/
theorem isZero_homology_pullback_of_bounded_locallyFree_acyclic
    {Y Z : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℤ) [P.IsStrictlyLE d]
    (hfree : ∀ n : ℤ, (P.X n).IsLocallyFree) (hP : P.Acyclic) (g : Z ⟶ Y) (q : ℤ) :
    IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P).homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    Scheme.Modules.exactAt_iff_stalkFunctor]
  intro z
  let R := Y.presheaf.stalk (g z)
  let S := Z.presheaf.stalk z
  let φ : R →+* S := (g.stalkMap z).hom
  letI : Algebra R S := φ.toAlgebra
  let C : CochainComplex (ModuleCat.{u} R) ℤ :=
    ((stalkModulesFunctor (g z)).mapHomologicalComplex (.up ℤ)).obj P
  have hC : C.Acyclic := acyclic_stalkModulesFunctor_of_acyclic P hP (g z)
  haveI : C.IsStrictlyLE d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact (stalkModulesFunctor (g z)).map_isZero
      (CochainComplex.isZero_of_isStrictlyLE P d n hn)
  haveI : ∀ n : ℤ, Module.Free R (C.X n) := fun n => by
    haveI := hfree n
    exact free_stalkModulesFunctor_of_locallyFree (P.X n) (g z)
  let Q : CochainComplex Z.Modules ℤ :=
    ((Scheme.Modules.pullback g).mapHomologicalComplex (.up ℤ)).obj P
  let D : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((stalkModulesFunctor z).mapHomologicalComplex (.up ℤ)).obj Q
  let E : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj C
  let e (n : ℤ) : E.X n ≃ₗ[S] D.X n :=
    (ModuleCat.tensorEquivExtendScalars R S (C.X n)).symm.trans
      (LinearEquiv.ofBijective (Scheme.Modules.pullbackStalkMap g z (P.X n))
        (Scheme.Modules.bijective_pullbackStalkMap g z (P.X n)))
  let comparison : E ⟶ D :=
    { f := fun n => (e n).toModuleIso.hom
      comm' := by
        intro i j hij
        ext a
        symm
        change Scheme.Modules.pullbackStalkMap g z (P.X j)
            ((ModuleCat.tensorEquivExtendScalars R S (C.X j)).symm
              ((ModuleCat.extendScalars φ).map (C.d i j) a)) =
          ((Scheme.Modules.pullback g).map (P.d i j)).stalkLinearMap z
            (Scheme.Modules.pullbackStalkMap g z (P.X i)
              ((ModuleCat.tensorEquivExtendScalars R S (C.X i)).symm a))
        erw [ModuleCat.tensorEquivExtendScalars_symm_naturality]
        exact Scheme.Modules.pullbackStalkMap_naturality g z (P.d i j) _ }
  haveI (n : ℤ) : IsIso (comparison.f n) := by
    change IsIso (e n).toModuleIso.hom
    infer_instance
  haveI : IsIso comparison := HomologicalComplex.Hom.isIso_of_components comparison
  have hE : IsZero (E.homology q) :=
    isZero_homology_extendScalars_of_bounded_free_acyclic R S φ C d hC q
  have hD : IsZero (D.homology q) := hE.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) q).mapIso (asIso comparison)).symm
  have hex : D.ExactAt q := (HomologicalComplex.exactAt_iff_isZero_homology D q).mpr hD
  exact (HomologicalComplex.exactAt_iff _ q).mpr
    (((HomologicalComplex.exactAt_iff D q).mp hex).map
      (forget₂ (ModuleCat S) AddCommGrpCat))

end ZInQ.Contrib.CloudR2Poincare.L3
