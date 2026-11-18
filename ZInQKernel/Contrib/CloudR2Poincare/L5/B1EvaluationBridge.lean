import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Field
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Homology.CochainComplex.RestrictScalars

/-!
# B1: classical module-evaluation cohomology versus native abelian-sheaf Ext

The inspected Stacks Kunneth theorem uses right-derived module evaluation;
L1's target uses the ACTUAL W07 `N.H q` groups. This file constructs the
comparison through a chosen injective resolution, an exact field-spectrum
sections functor, and the already proved native higher-direct-image comparison.
No identification of those groups, Kunneth formula, or vanishing is assumed.

Original lane-local proof. All nonowned dependencies are native W07 modules,
not the unbuilt 2029-module Stacks Kunneth closure.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace ZInQ.Contrib.CloudR2Poincare.L5

section General

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [Abelian E]

/-- Exact postcomposition commutes with right derivation, proved on an actual
injective resolution rather than assumed as a carried comparison. -/
def rightDerivedPostcomposeIso (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive] [G.PreservesHomology] (M : C) (q : ℕ) :
    G.obj ((F.rightDerived q).obj M) ≅ ((F ⋙ G).rightDerived q).obj M := by
  let I := injectiveResolution M
  exact G.mapIso (I.isoRightDerivedObj F q) ≪≫
    ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc q).mapHomologyIso G).symm ≪≫
      (I.isoRightDerivedObj (F ⋙ G) q).symm

/-- A natural functor isomorphism gives the componentwise right-derived
isomorphism, using a literal isomorphism of the two resolution complexes. -/
def rightDerivedNatIsoComponent (F G : C ⥤ D) [F.Additive] [G.Additive]
    (e : F ≅ G) (M : C) (q : ℕ) :
    ((F.rightDerived q).obj M) ≅ ((G.rightDerived q).obj M) := by
  let I := injectiveResolution M
  let comparison :
      (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
        (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
    { hom :=
        { f i := e.hom.app (I.cocomplex.X i)
          comm' i j _ := (e.hom.naturality (I.cocomplex.d i j)).symm }
      inv :=
        { f i := e.inv.app (I.cocomplex.X i)
          comm' i j _ := (e.inv.naturality (I.cocomplex.d i j)).symm }
      hom_inv_id := by ext i; simp
      inv_hom_id := by ext i; simp }
  exact I.isoRightDerivedObj F q ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℕ) q).mapIso comparison ≪≫
      (I.isoRightDerivedObj G q).symm

end General

universe u

/-- Actual addition of module-sheaf morphisms is preserved by evaluation.
Used only as a local proof instance, not as a cohomology-model hypothesis. -/
theorem nativeModuleEvaluationAdditive {X : Scheme.{u}} (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive :=
  { map_add := rfl }

attribute [local instance] nativeModuleEvaluationAdditive

/-- The scalar ring map used in the inspected Stacks Cech Kunneth
`structureRingHom` is exactly the native field-action ring map. -/
theorem nativeStructureRingHom_eq_appLE
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] :
    (((X ↘ Spec (.of k)).appLE ⊤ ⊤ le_top).hom.comp
      (Scheme.ΓSpecIso (.of k)).inv.hom) =
        Scheme.globalSectionsRingHom k (X := X) := by
  have appComparison : (X ↘ Spec (.of k)).appLE ⊤ ⊤ le_top =
      (X ↘ Spec (.of k)).app ⊤ :=
    (X ↘ Spec (.of k)).appLE_eq_app (U := ⊤)
  rw [appComparison]
  rfl

/-- The original-field sections functor expressed either through the field
spectrum or by restriction of scalars from the native module evaluation. -/
def pushforwardFieldSectionsIso
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] :
    Scheme.Modules.pushforward (X ↘ Spec (.of k)) ⋙ moduleSpecΓFunctor (R := .of k) ≅
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X)) :=
  NatIso.ofComponents (fun N => LinearEquiv.toModuleIso
    (X₁ := (Scheme.Modules.pushforward (X ↘ Spec (.of k)) ⋙
      moduleSpecΓFunctor (R := .of k)).obj N)
    (X₂ := (SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))).obj N)
    { toFun x := x
      invFun x := x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }) (by intro N M f; ext x; rfl)

/-- The genuine missing cohomology-model bridge needed to use the inspected
Stacks Kunneth theorem in L1's native `N.H q` rank statement. -/
theorem native_H_classicalEvaluation_linearEquiv
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (N : X.Modules) [N.IsQuasicoherent] (q : ℕ) :
    Nonempty ((ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := X))).obj
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived q).obj N)
        ≃ₗ[k] N.H q) := by
  let f := X ↘ Spec (.of k)
  let F := Scheme.Modules.pushforward f
  let G := moduleSpecΓFunctor (R := .of k)
  let A := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let S := ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))
  haveI : G.Additive := AlgebraicGeometry.moduleSpecΓFunctorAdditive
  haveI : G.IsEquivalence := AlgebraicGeometry.isEquivalence_moduleSpecΓFunctor
    (Field.toIsField k)
  haveI : G.PreservesHomology := inferInstance
  haveI : S.PreservesHomology := inferInstance
  haveI : (A ⋙ S).Additive := { map_add := rfl }
  let derivedComparison :
      G.obj ((F.rightDerived q).obj N) ≅ S.obj ((A.rightDerived q).obj N) :=
    rightDerivedPostcomposeIso F G N q ≪≫
      rightDerivedNatIsoComponent (F ⋙ G) (A ⋙ S) pushforwardFieldSectionsIso N q ≪≫
        (rightDerivedPostcomposeIso A S N q).symm
  obtain ⟨nativeComparison⟩ :=
    Scheme.Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H N k q
  exact ⟨derivedComparison.symm.toLinearEquiv.trans nativeComparison⟩

/-- The comparison is for the complete native field action and therefore
identifies ranks, not merely abelian-group carriers. -/
theorem native_finrankH_classicalEvaluation
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (N : X.Modules) [N.IsQuasicoherent] (q : ℕ) :
    Module.finrank k ((ModuleCat.restrictScalars
      (Scheme.globalSectionsRingHom k (X := X))).obj
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived q).obj N)) =
        N.finrankH k q := by
  obtain ⟨comparison⟩ := native_H_classicalEvaluation_linearEquiv (k := k) N q
  exact comparison.finrank_eq

end ZInQ.Contrib.CloudR2Poincare.L5
