import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceMaps
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechCohomology

/-!
# Coefficient-natural native explicit Čech maps

Actual coefficient maps act on ALL tuple cochains. The comparison with the
underlying abelian explicit Čech complex is a literal componentwise identity,
not a rank-selected equivalence. These maps support coefficient-natural
Čech/native-H comparisons and the actual face/pushforward factorization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace TopCat.Presheaf

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The ACTUAL coefficient map on native Čech cochains. -/
def cechCoefficientCochainLinearMap
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q M (⨅ l, U (t l))) →ₗ[Γ(S, ⊤)]
      (∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q N (⨅ l, U (t l))) :=
  LinearMap.pi fun t ↦ coefficientSectionsLinearMap q φ (⨅ l, U (t l)) ∘ₗ LinearMap.proj t

@[simp]
theorem cechCoefficientCochainLinearMap_apply
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : ∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q M (⨅ l, U (t l)))
    (t : Fin (n + 1) → ι) :
    cechCoefficientCochainLinearMap q φ U n c t = φ.app (⨅ l, U (t l)) (c t) := rfl

/-- Coefficient naturality for the FULL non-alternating differential. -/
theorem cechCoefficientCochainLinearMap_d
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : ∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q M (⨅ l, U (t l))) :
    cechCoefficientCochainLinearMap q φ U (n + 1) (Scheme.Modules.cechModuleD q M U n c) =
      Scheme.Modules.cechModuleD q N U n (cechCoefficientCochainLinearMap q φ U n c) := by
  funext t
  simp only [cechCoefficientCochainLinearMap_apply, Scheme.Modules.cechModuleD_apply_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  congr 1
  exact Scheme.Modules.Hom.app_presheaf_map φ (homOfLE (iInf_le_iInf_comp U t i.succAbove)) _

/-- The ACTUAL native coefficient chain map on Nat-indexed Čech complexes. -/
def cechModuleCoefficientMapNat
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplexNat q M U ⟶ Scheme.Modules.cechModuleComplexNat q N U where
  f n := ModuleCat.ofHom (cechCoefficientCochainLinearMap q φ U n)
  comm' := by
    rintro n _ rfl
    rw [Scheme.Modules.cechModuleComplexNat_d, Scheme.Modules.cechModuleComplexNat_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (cechCoefficientCochainLinearMap_d q φ U n c).symm

/-- The ACTUAL coefficient arrow between the original integer complexes. -/
def cechModuleCoefficientMap
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplex q M U ⟶ Scheme.Modules.cechModuleComplex q N U :=
  HomologicalComplex.extendMap (cechModuleCoefficientMapNat q φ U) ComplexShape.embeddingUpNat

/-- Literal identification of the native module Čech complex after forgetting
scalars with the underlying abelian explicit Čech complex. -/
def cechModuleNatForgetAbIso
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (Scheme.Modules.cechModuleComplexNat q M U) ≅
      (TopCat.Presheaf.cechComplex U).obj M.presheaf :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _) (by
    rintro n _ rfl
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.ext
    intro c
    change (ConcreteCategory.hom (((TopCat.Presheaf.cechComplex U).obj M.presheaf).d n (n + 1))) c =
      ((Scheme.Modules.cechModuleComplexNat q M U).d n (n + 1)).hom c
    rw [Scheme.Modules.cechModuleComplexNat_d]
    exact (Scheme.Modules.cechModuleD_apply q M U n c).symm)

/-- The literal comparison respects the ACTUAL coefficient map, not an
arbitrarily selected isomorphism on homology. -/
theorem cechModuleNatForgetAbIso_naturality
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) :
    ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (cechModuleCoefficientMapNat q φ U) ≫ (cechModuleNatForgetAbIso q N U).hom =
      (cechModuleNatForgetAbIso q M U).hom ≫
        (TopCat.Presheaf.cechComplex U).map ((Scheme.Modules.toPresheaf X).map φ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro c
  funext t
  rfl

/-- Actual native Čech homology is the underlying abelian Čech cohomology,
through the canonical forgetful homology comparison. -/
def cechModuleNatHomologyAbIso
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).obj
      ((Scheme.Modules.cechModuleComplexNat q M U).homology n) ≅
      ((TopCat.Presheaf.cechComplex U).obj M.presheaf).homology n :=
  (((Scheme.Modules.cechModuleComplexNat q M U).sc n).mapHomologyIso (forget₂ _ _)).symm ≪≫
    HomologicalComplex.homologyMapIso (cechModuleNatForgetAbIso q M U) n

end ZInQ.Contrib.CloudR2Poincare.L1
