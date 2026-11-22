import ZInQKernel.Contrib.CloudR2Poincare.L1.CechCoefficientMaps

/-!
# Actual face/pushforward factorization of the original native Čech map

The face complex is identified with the ambient Čech complex of the ACTUAL
pushforward coefficient. Components are actual pushforward sections and
canonical equality-of-opens transports. The native face arrow then factors
through the ACTUAL pullback-pushforward adjunction unit, at the chain level.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace TopCat.Presheaf

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual pushforward restriction, after the same canonical open transports
used by the native face map. -/
theorem pushforwardSections_transport_restrict
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules)
    {U V : X.Opens} {U' V' : Y.Opens} (h : V ≤ U)
    (hU : j ⁻¹ᵁ U = U') (hV : j ⁻¹ᵁ V = V') (h' : V' ≤ U')
    (s : Scheme.Modules.sectionsModule q ((Scheme.Modules.pushforward j).obj N) U) :
    faceOpenEqLinearEquiv (j ≫ q) N hV
        (pushforwardSectionsLinearEquiv q j N V
          (Scheme.Modules.sectionsModuleRestrict q ((Scheme.Modules.pushforward j).obj N) h s)) =
      Scheme.Modules.sectionsModuleRestrict (j ≫ q) N h'
        (faceOpenEqLinearEquiv (j ≫ q) N hU (pushforwardSectionsLinearEquiv q j N U s)) := by
  subst U'
  subst V'
  simp only [faceOpenEqLinearEquiv_refl]
  rfl

/-- Actual identification on ALL tuple cochains. -/
def cechPushforwardCochainLinearEquiv
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q ((Scheme.Modules.pushforward j).obj N)
        (⨅ l, U (t l))) ≃ₗ[Γ(S, ⊤)]
      (∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule (j ≫ q) N
        (⨅ l, j ⁻¹ᵁ U (t l))) :=
  LinearEquiv.piCongrRight fun t ↦
    (pushforwardSectionsLinearEquiv q j N (⨅ l, U (t l))).trans
      (faceOpenEqLinearEquiv (j ≫ q) N (face_preimage_iInf j (fun l ↦ U (t l))))

@[simp]
theorem cechPushforwardCochainLinearEquiv_apply
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : ∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q ((Scheme.Modules.pushforward j).obj N)
      (⨅ l, U (t l))) (t : Fin (n + 1) → ι) :
    cechPushforwardCochainLinearEquiv q j N U n c t =
      faceOpenEqLinearEquiv (j ≫ q) N (face_preimage_iInf j (fun l ↦ U (t l)))
        (pushforwardSectionsLinearEquiv q j N (⨅ l, U (t l)) (c t)) := rfl

/-- The identification respects the FULL original Čech differential. -/
theorem cechPushforwardCochainLinearEquiv_d
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : ∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q ((Scheme.Modules.pushforward j).obj N)
      (⨅ l, U (t l))) :
    cechPushforwardCochainLinearEquiv q j N U (n + 1)
        (Scheme.Modules.cechModuleD q ((Scheme.Modules.pushforward j).obj N) U n c) =
      Scheme.Modules.cechModuleD (j ≫ q) N (fun i ↦ j ⁻¹ᵁ U i) n
        (cechPushforwardCochainLinearEquiv q j N U n c) := by
  funext t
  simp only [cechPushforwardCochainLinearEquiv_apply, Scheme.Modules.cechModuleD_apply_apply]
  change (faceOpenEqLinearEquiv (j ≫ q) N (face_preimage_iInf j (fun l ↦ U (t l))))
      ((pushforwardSectionsLinearEquiv q j N (⨅ l, U (t l)))
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          Scheme.Modules.sectionsModuleRestrict q ((Scheme.Modules.pushforward j).obj N)
            (iInf_le_iInf_comp U t i.succAbove) (c (t ∘ i.succAbove)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul]
  congr 1
  exact pushforwardSections_transport_restrict q j N (iInf_le_iInf_comp U t i.succAbove)
    (face_preimage_iInf j (fun l ↦ U ((t ∘ i.succAbove) l)))
    (face_preimage_iInf j (fun l ↦ U (t l)))
    (iInf_le_iInf_comp (fun a ↦ j ⁻¹ᵁ U a) t i.succAbove) (c (t ∘ i.succAbove))

/-- The ACTUAL native face Čech complex is the ambient complex of pushforward. -/
def cechModulePushforwardIsoNat
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplexNat q ((Scheme.Modules.pushforward j).obj N) U ≅
      Scheme.Modules.cechModuleComplexNat (j ≫ q) N (fun i ↦ j ⁻¹ᵁ U i) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (cechPushforwardCochainLinearEquiv q j N U n).toModuleIso) (by
      rintro n _ rfl
      rw [Scheme.Modules.cechModuleComplexNat_d, Scheme.Modules.cechModuleComplexNat_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (cechPushforwardCochainLinearEquiv_d q j N U n c).symm)

/-- The ACTUAL factorization through the native coefficient unit, before any
homology or dimension computation. -/
theorem cechModuleFaceMapNat_factorization
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    cechModuleFaceMapNat q j M U =
      cechModuleCoefficientMapNat q ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) U ≫
        (cechModulePushforwardIsoNat q j ((Scheme.Modules.pullback j).obj M) U).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext t
  rfl

/-- The identification retains the ORIGINAL unbounded non-alternating complexes. -/
def cechModulePushforwardIso
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplex q ((Scheme.Modules.pushforward j).obj N) U ≅
      Scheme.Modules.cechModuleComplex (j ≫ q) N (fun i ↦ j ⁻¹ᵁ U i) :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} Γ(S, ⊤))).mapIso
    (cechModulePushforwardIsoNat q j N U)

/-- Original-complex ACTUAL coefficient-unit factorization. -/
theorem cechModuleFaceMap_factorization
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    cechModuleFaceMap q j M U =
      cechModuleCoefficientMap q ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) U ≫
        (cechModulePushforwardIso q j ((Scheme.Modules.pullback j).obj M) U).hom := by
  change HomologicalComplex.extendMap (cechModuleFaceMapNat q j M U) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (cechModuleCoefficientMapNat q ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) U)
      ComplexShape.embeddingUpNat ≫ HomologicalComplex.extendMap
        (cechModulePushforwardIsoNat q j ((Scheme.Modules.pullback j).obj M) U).hom
        ComplexShape.embeddingUpNat
  rw [cechModuleFaceMapNat_factorization, HomologicalComplex.extendMap_comp]

end ZInQ.Contrib.CloudR2Poincare.L1
