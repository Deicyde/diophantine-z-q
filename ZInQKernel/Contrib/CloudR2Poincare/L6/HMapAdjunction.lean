import ZInQKernel.Contrib.CloudR2Poincare.L6.HPullbackBasic
import ZInQKernel.Contrib.CloudR2Poincare.L6.ExtFunctorCoherence
import ZInQKernel.Contrib.CloudR2Poincare.L6.AdjunctionMapCoherence
import ZInQKernel.Contrib.CloudR2Poincare.L4.HPullback.Coherence

/-!
# Composition of the EXISTING native cohomological adjunction maps

Actual exact inverse image, literal W07 integer theta, native coefficient
adjunctions and the certified L4 composition mate are used throughout.
No replacement cohomology map, flatness premise or rank model is introduced.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w₀ w₁ w₂
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.Abelian
open ZInQ.Contrib.CloudR2Poincare.L4.HPullback

namespace ZInQ.Contrib.CloudR2Poincare.L6

section ExtCalculus
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasExt.{w₀} C] [HasExt.{w₁} D] [HasExt.{w₂} E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Actual pointed Ext-map composition including the actual coefficient maps. -/
theorem pointedExtWithCoeff_comp {K M : C} {K' N : D} {K'' P : E} (q : ℕ)
    (a : K' ⟶ F.obj K) (b : K'' ⟶ G.obj K')
    (c : F.obj M ⟶ N) (d : G.obj N ⟶ P) (z : Ext.{w₀} K M q) :
    ((Ext.mk₀ b).comp
        ((((Ext.mk₀ a).comp (z.mapExactFunctor F) (zero_add q)).comp
          (Ext.mk₀ c) (add_zero q)).mapExactFunctor G) (zero_add q)).comp
        (Ext.mk₀ d) (add_zero q) =
      ((Ext.mk₀ (b ≫ G.map a)).comp (z.mapExactFunctor (F ⋙ G)) (zero_add q)).comp
        (Ext.mk₀ (G.map c ≫ d)) (add_zero q) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, pointedExtMap_comp F G,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

variable (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- Coherent source/coefficient arrows identify the actual composite with a native functor iso. -/
theorem pointedExtWithCoeff_comp_iso {K M : C} {K' N : D} {K'' P : E}
    (q : ℕ) (α : F ⋙ G ≅ H)
    (a : K' ⟶ F.obj K) (b : K'' ⟶ G.obj K') (e : K'' ⟶ H.obj K)
    (c : F.obj M ⟶ N) (d : G.obj N ⟶ P) (h : H.obj M ⟶ P)
    (source : (b ≫ G.map a) ≫ α.hom.app K = e)
    (coefficient : G.map c ≫ d = α.hom.app M ≫ h)
    (z : Ext.{w₀} K M q) :
    ((Ext.mk₀ b).comp
        ((((Ext.mk₀ a).comp (z.mapExactFunctor F) (zero_add q)).comp
          (Ext.mk₀ c) (add_zero q)).mapExactFunctor G) (zero_add q)).comp
        (Ext.mk₀ d) (add_zero q) =
      ((Ext.mk₀ e).comp (z.mapExactFunctor H) (zero_add q)).comp
        (Ext.mk₀ h) (add_zero q) := by
  rw [pointedExtWithCoeff_comp F G, coefficient]
  have hn := pointedExtMap_natTrans (F ⋙ G) H q (b ≫ G.map a) α.hom z
  rw [source] at hn
  calc
    ((Ext.mk₀ (b ≫ G.map a)).comp (z.mapExactFunctor (F ⋙ G)) (zero_add q)).comp
        (Ext.mk₀ (α.hom.app M ≫ h)) (add_zero q) =
      (((Ext.mk₀ (b ≫ G.map a)).comp (z.mapExactFunctor (F ⋙ G)) (zero_add q)).comp
        (Ext.mk₀ (α.hom.app M)) (add_zero q)).comp (Ext.mk₀ h) (add_zero q) := by
          rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    _ = _ := congrArg (fun v => v.comp (Ext.mk₀ h) (add_zero q)) hn

end ExtCalculus

/-- Forgetting the actual module-pushforward composition coefficient gives the actual abelian iso. -/
theorem nativePushforwardComp_toSheaf {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (M : X.Modules) :
    (SheafOfModules.toSheaf Z.ringCatSheaf).map
        ((Scheme.Modules.pushforwardComp a b).hom.app M) =
      (abelianPushforwardCompIso a b).hom.app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  ext U s
  rfl

private theorem default_pushforwardCompCoefficient_toSheaf
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    {M : Z.Modules} {N : Y.Modules} {P : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward b).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward a).obj P) :
    (SheafOfModules.toSheaf Z.ringCatSheaf).map
      (φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
        (Scheme.Modules.pushforwardComp a b).hom.app P) =
      (SheafOfModules.toSheaf Z.ringCatSheaf).map φ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).map
          ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ) ≫
        (abelianPushforwardCompIso a b).hom.app
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj P) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    nativePushforwardComp_toSheaf]
  rfl

/-- The actual two adjoint coefficient maps compose through the same audited abelian alpha. -/
theorem nativeAdjointCoefficientMap_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) {M : Z.Modules} {N : Y.Modules} {P : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward b).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward a).obj P) :
    (Scheme.Modules.abelianInverseImage a).map (Scheme.Modules.adjointCoefficientMap b φ) ≫
        Scheme.Modules.adjointCoefficientMap a ψ =
      (abelianInverseImageCompIso a b).hom.app
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M) ≫
      Scheme.Modules.adjointCoefficientMap (a ≫ b)
        (φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
          (Scheme.Modules.pushforwardComp a b).hom.app P) := by
  have hc := default_pushforwardCompCoefficient_toSheaf a b φ ψ
  have h := adjunct_comp_leftCompIso
    (abelianInverseImageAdjunction b) (abelianInverseImageAdjunction a)
    (abelianInverseImageAdjunction (a ≫ b)) (abelianPushforwardCompIso a b)
    (X := (SheafOfModules.toSheaf Z.ringCatSheaf).obj M)
    (Y := (SheafOfModules.toSheaf Y.ringCatSheaf).obj N)
    (Z := (SheafOfModules.toSheaf X.ringCatSheaf).obj P)
    ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ)
    ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ)
  change (Scheme.Modules.abelianInverseImage a).map
        (Scheme.Modules.adjointCoefficientMap b φ) ≫
      Scheme.Modules.adjointCoefficientMap a ψ =
    (abelianInverseImageCompIso a b).hom.app
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M) ≫
      ((abelianInverseImageAdjunction (a ≫ b)).homEquiv _ _).symm
        ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} b.base).map
            ((SheafOfModules.toSheaf Y.ringCatSheaf).map ψ) ≫
          (abelianPushforwardCompIso a b).hom.app
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj P)) at h
  rw [← hc] at h
  exact h

/-- The audited constant source-arrow inverse coherence, in the orientation used by H.mapFunctor. -/
theorem nativeConstantSource_comp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    ((Scheme.Modules.abelianInverseImageConstantIso a).inv ≫
        (Scheme.Modules.abelianInverseImage a).map
          (Scheme.Modules.abelianInverseImageConstantIso b).inv) ≫
        (abelianInverseImageCompIso a b).hom.app (abelianConstantIntegerSheaf Z) =
      (Scheme.Modules.abelianInverseImageConstantIso (a ≫ b)).inv := by
  have hm : (Scheme.Modules.abelianInverseImage a).map
      (Scheme.Modules.abelianInverseImageConstantIso b).inv ≫
        (Scheme.Modules.abelianInverseImage a).map
          (Scheme.Modules.abelianInverseImageConstantIso b).hom = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  apply (cancel_mono (Scheme.Modules.abelianInverseImageConstantIso (a ≫ b)).hom).mp
  simp only [Category.assoc]
  rw [← abelianInverseImageConstantIso_comp a b]
  calc
    (Scheme.Modules.abelianInverseImageConstantIso a).inv ≫
        (Scheme.Modules.abelianInverseImage a).map
          (Scheme.Modules.abelianInverseImageConstantIso b).inv ≫
        (Scheme.Modules.abelianInverseImage a).map
          (Scheme.Modules.abelianInverseImageConstantIso b).hom ≫
        (Scheme.Modules.abelianInverseImageConstantIso a).hom =
      (Scheme.Modules.abelianInverseImageConstantIso a).inv ≫
        ((Scheme.Modules.abelianInverseImage a).map
          (Scheme.Modules.abelianInverseImageConstantIso b).inv ≫
         (Scheme.Modules.abelianInverseImage a).map
          (Scheme.Modules.abelianInverseImageConstantIso b).hom) ≫
        (Scheme.Modules.abelianInverseImageConstantIso a).hom := by
          simp only [Category.assoc]
    _ = _ := by
      rw [hm, Category.id_comp, Iso.inv_hom_id]
      exact (Scheme.Modules.abelianInverseImageConstantIso (a ≫ b)).inv_hom_id.symm

/-- Expose one native adjunction application using the existing sheaf-map
application lemmas. The composition proof rewrites these applications before
matching the pointed Ext equality, instead of unfolding nested maps in exact. -/
private theorem e2_nativeHMapOfAdjunction_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) (q : ℕ)
    (z : Ext.{u} (abelianConstantIntegerSheaf Y)
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) q) :
    Scheme.Modules.H.mapOfAdjunction f φ q z =
      ((Ext.mk₀ (Scheme.Modules.abelianInverseImageConstantIso f).inv).comp
        (z.mapExactFunctor (Scheme.Modules.abelianInverseImage f)) (zero_add q)).comp
        (Ext.mk₀ (Scheme.Modules.adjointCoefficientMap f φ)) (add_zero q) := by
  unfold Scheme.Modules.H.mapOfAdjunction
  rfl

/-- Composition of the EXISTING Ext-defined adjunction cohomology maps, for every scheme morphism. -/
theorem nativeHMapOfAdjunction_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) {M : Z.Modules} {N : Y.Modules} {P : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward b).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward a).obj P) (q : ℕ) (z : M.H q) :
    Scheme.Modules.H.mapOfAdjunction a ψ q
        (Scheme.Modules.H.mapOfAdjunction b φ q z) =
      Scheme.Modules.H.mapOfAdjunction (a ≫ b)
        (φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
          (Scheme.Modules.pushforwardComp a b).hom.app P) q z := by
  let z' : Ext.{u} (abelianConstantIntegerSheaf Z)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M) q := z
  have h := pointedExtWithCoeff_comp_iso
    (Scheme.Modules.abelianInverseImage b) (Scheme.Modules.abelianInverseImage a)
    (Scheme.Modules.abelianInverseImage (a ≫ b))
    (K := abelianConstantIntegerSheaf Z)
    (M := (SheafOfModules.toSheaf Z.ringCatSheaf).obj M)
    (K' := abelianConstantIntegerSheaf Y)
    (N := (SheafOfModules.toSheaf Y.ringCatSheaf).obj N)
    (K'' := abelianConstantIntegerSheaf X)
    (P := (SheafOfModules.toSheaf X.ringCatSheaf).obj P)
    q (abelianInverseImageCompIso a b)
    (Scheme.Modules.abelianInverseImageConstantIso b).inv
    (Scheme.Modules.abelianInverseImageConstantIso a).inv
    (Scheme.Modules.abelianInverseImageConstantIso (a ≫ b)).inv
    (Scheme.Modules.adjointCoefficientMap b φ) (Scheme.Modules.adjointCoefficientMap a ψ)
    (Scheme.Modules.adjointCoefficientMap (a ≫ b)
      (φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
        (Scheme.Modules.pushforwardComp a b).hom.app P))
    (nativeConstantSource_comp a b) (nativeAdjointCoefficientMap_comp a b φ ψ) z'
  rw [e2_nativeHMapOfAdjunction_apply a ψ q
      (Scheme.Modules.H.mapOfAdjunction b φ q z),
    e2_nativeHMapOfAdjunction_apply b φ q z,
    e2_nativeHMapOfAdjunction_apply (a ≫ b)
      (φ ≫ (Scheme.Modules.pushforward b).map ψ ≫
        (Scheme.Modules.pushforwardComp a b).hom.app P) q z]
  dsimp only [z'] at h
  exact h

/-- Postcomposing the actual coefficient arrow is postcomposition on the native cohomology map. -/
theorem nativeHMapOfAdjunction_postcompose {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {N P : X.Modules} (φ : M ⟶ (Scheme.Modules.pushforward f).obj N)
    (ψ : N ⟶ P) (q : ℕ) (z : M.H q) :
    Scheme.Modules.H.map ψ q (Scheme.Modules.H.mapOfAdjunction f φ q z) =
      Scheme.Modules.H.mapOfAdjunction f (φ ≫ (Scheme.Modules.pushforward f).map ψ) q z := by
  have h := Scheme.Modules.H.mapOfAdjunction_naturality f φ
    (φ ≫ (Scheme.Modules.pushforward f).map ψ) (𝟙 M) ψ (by simp) q z
  simpa only [Scheme.Modules.H.map_id_apply] using h.symm

/-- Forgetting the actual module identity-pushforward iso gives the native abelian identity iso. -/
theorem nativePushforwardId_toSheaf (X : Scheme.{u}) (M : X.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pushforwardId X).inv.app M) =
      (abelianPushforwardIdIso X).inv.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  ext U s
  rfl

/-- The actual identity adjoint coefficient map is the canonical inverse-image identity alpha. -/
theorem nativeAdjointCoefficientMap_id (X : Scheme.{u}) (M : X.Modules) :
    Scheme.Modules.adjointCoefficientMap (𝟙 X) ((Scheme.Modules.pushforwardId X).inv.app M) =
      (abelianInverseImageIdIso X).hom.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  unfold Scheme.Modules.adjointCoefficientMap
  rw [nativePushforwardId_toSheaf]
  simp only [Adjunction.homEquiv_counit, abelianInverseImageIdIso,
    Adjunction.leftAdjointIdIso_hom_app]
  rfl

/-- Identity for the EXISTING native H.mapOfAdjunction, with its actual pushforward identity coefficient. -/
theorem nativeHMapOfAdjunction_id (X : Scheme.{u}) (M : X.Modules) (q : ℕ) (z : M.H q) :
    Scheme.Modules.H.mapOfAdjunction (𝟙 X) ((Scheme.Modules.pushforwardId X).inv.app M) q z = z := by
  let z' : Ext.{u} (abelianConstantIntegerSheaf X)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) q := z
  have hn := pointedExtMap_natTrans (Scheme.Modules.abelianInverseImage (𝟙 X))
    (𝟭 (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (K := abelianConstantIntegerSheaf X)
    (M := (SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (K' := abelianConstantIntegerSheaf X)
    q (Scheme.Modules.abelianInverseImageConstantIso (𝟙 X)).inv
    (abelianInverseImageIdIso X).hom z'
  have hs : (Scheme.Modules.abelianInverseImageConstantIso (𝟙 X)).inv ≫
      (abelianInverseImageIdIso X).hom.app (abelianConstantIntegerSheaf X) = 𝟙 _ := by
    rw [← abelianInverseImageConstantIso_id X]
    exact Iso.inv_hom_id _
  rw [hs] at hn
  have he := hn.trans (pointedExtMap_id q z')
  have h : ((Ext.mk₀ (Scheme.Modules.abelianInverseImageConstantIso (𝟙 X)).inv).comp
      (z'.mapExactFunctor (Scheme.Modules.abelianInverseImage (𝟙 X))) (zero_add q)).comp
        (Ext.mk₀ (Scheme.Modules.adjointCoefficientMap (𝟙 X)
          ((Scheme.Modules.pushforwardId X).inv.app M))) (add_zero q) = z' := by
    rw [nativeAdjointCoefficientMap_id]
    exact he
  exact h

end ZInQ.Contrib.CloudR2Poincare.L6
