import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq.lean
Original Git blob: 4fdf39ea770f62f21b24b9778e68e530cdeff7da
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

open TopologicalSpace

namespace BenchOB4
h77_bridge_namespace

theorem map_map {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (k : W ⟶ U)
    (x : Γ(M, U)) : M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  congr 2

theorem sec_ext {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (Wi : ι → X.Opens) (V : X.Opens)
    (hle : ∀ i, Wi i ≤ V) (hcover : ∀ x ∈ V, ∃ i, x ∈ Wi i) (s t : Γ(M, V))
    (h : ∀ i, M.presheaf.map (homOfLE (hle i)).op s = M.presheaf.map (homOfLE (hle i)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, Scheme.Modules.isSheaf M⟩ Wi V (fun i => homOfLE (hle i))
    (fun x hx => by obtain ⟨i, hi⟩ := hcover x hx; exact Opens.mem_iSup.mpr ⟨i, hi⟩) s t h

theorem app_naturality {X : Scheme.{u}} {M N : X.Modules} (θ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V)
    (x : Γ(M, V)) :
    N.presheaf.map i.op (θ.app V x) = θ.app W (M.presheaf.map i.op x) := by
  have h := θ.mapPresheaf.naturality i.op
  have h' := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, V) → Γ(N, W))) h) x
  exact h'.symm

theorem algebraMap_comm {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (U : Y.Opens) (W : X.Opens) (hWU : W ≤ φ ⁻¹ᵁ U) (a : A) :
    (φ.appLE U W hWU) (((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf gY).app (op U)) a) =
      ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf gX).app (op W)) (algebraMap A B a) := by
  have hc : ∀ {h₁ h₂ : X ⟶ Spec (CommRingCat.of A)} (_ : h₁ = h₂) (e₁ : W ≤ h₁ ⁻¹ᵁ ⊤)
      (e₂ : W ≤ h₂ ⁻¹ᵁ ⊤), h₁.appLE ⊤ W e₁ = h₂.appLE ⊤ W e₂ := by
    rintro _ _ rfl _ _; rfl
  have h1 : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf gY).app (op U) ≫ φ.appLE U W hWU =
      CommRingCat.ofHom (algebraMap A B) ≫ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf gX).app (op W) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top) ≫ φ.appLE U W hWU =
      CommRingCat.ofHom (algebraMap A B) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ gX.appLE ⊤ W le_top)
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, hc hφ _ le_top,
      ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top]
    have h2 : (Spec.map (CommRingCat.ofHom (algebraMap A B))).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop := by
      simp [Scheme.Hom.appLE]
    rw [h2, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have := congrFun (congrArg (fun f => (ConcreteCategory.hom f : A → Γ(X, W))) h1) a
  simpa using this

end BenchOB4

theorem solution
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    {X Y Z : Scheme.{u}} (gZ : Z ⟶ Spec (CommRingCat.of A)) (gY : Y ⟶ Spec (CommRingCat.of B))
    (gX : X ⟶ Spec (CommRingCat.of C))
    (ψ : Y ⟶ Z) (hψ : ψ ≫ gZ = gY ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (d : ℕ)
    (θψ : (Scheme.Modules.pullback ψ).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d) ⟶ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gY) d)
    (hθψ : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : IsAffineOpen W) (hWU : W ≤ ψ ⁻¹ᵁ U),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gZ) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) W
        letI : Algebra Γ(Z, U) Γ(Y, W) := (ψ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(Y, W)] [IsScalarTower A B Γ(Y, W)] [IsScalarTower A Γ(Z, U) Γ(Y, W)]
          (η : ⋀[Γ(Z, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gZ).obj (op U))),
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gY) d).presheaf.map (homOfLE hWU).op
              (θψ.app (ψ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection ψ ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gZ) d U η))) =
            (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gY) d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Z, U) Γ(Y, W) d η))
    (θφ : (Scheme.Modules.pullback φ).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gY) d) ⟶ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d)
    (hθφ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra B Γ(X, W)] [IsScalarTower B C Γ(X, W)] [IsScalarTower B Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gY).obj (op U))),
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d).presheaf.map (homOfLE hWU).op
              (θφ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gY) d U η))) =
            (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gX) d W (NeronModelInfra.TopFormOrder.topFormMap B C Γ(Y, U) Γ(X, W) d η))
    (θ : (Scheme.Modules.pullback (φ ≫ ψ)).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d) ⟶ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d)
    (hθ : ∀ (U : Z.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ (φ ≫ ψ) ⁻¹ᵁ U),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gZ) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W
        letI : Algebra Γ(Z, U) Γ(X, W) := ((φ ≫ ψ).appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A C Γ(X, W)] [IsScalarTower A Γ(Z, U) Γ(X, W)]
          (η : ⋀[Γ(Z, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gZ).obj (op U))),
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d).presheaf.map (homOfLE hWU).op
              (θ.app ((φ ≫ ψ) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gZ) d U η))) =
            (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gX) d W (NeronModelInfra.TopFormOrder.topFormMap A C Γ(Z, U) Γ(X, W) d η)) :
    θ = ((Scheme.Modules.pullbackComp φ ψ).app ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d)).inv ≫
      (Scheme.Modules.pullback φ).map θψ ≫ θφ := by
  have hφψ : (φ ≫ ψ) ≫ gZ = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [Category.assoc, hψ, ← Category.assoc, hφ, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq A B C]

  have e2 : ∀ (U : Z.Opens) (s : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d, U)),
      ((((Scheme.Modules.pullbackComp φ ψ).app ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d)).inv ≫
        (Scheme.Modules.pullback φ).map θψ ≫ θφ).app ((φ ≫ ψ) ⁻¹ᵁ U))
          (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) s) =
        θφ.app (φ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (Scheme.Modules.pullbackLocalSection φ
          (θψ.app (ψ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection ψ s))) := by
    intro U s
    have key : (((Scheme.Modules.pullbackComp φ ψ).app ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d)).inv).app ((φ ≫ ψ) ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection (φ ≫ ψ) s) =
        Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.pullbackLocalSection ψ s) :=
      congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d, U) →
          Γ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d)),
            (φ ≫ ψ) ⁻¹ᵁ U)))
        (Scheme.Modules.unit_app_comp_pullbackComp_inv φ ψ ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gZ) d) U)) s
    rw [Scheme.Modules.pullbackLocalSection_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
      CategoryTheory.comp_apply, CategoryTheory.comp_apply, key]
    rfl
  refine AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq gZ gX (φ ≫ ψ) hφψ d
    θ _ hθ ?_
  intro U hU W hW hWU iA iT₁ iT₂ η
  rw [e2 U ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gZ) d U η), ← hθ U hU W hW hWU η]

  let ι : Type u := {p : Y.affineOpens × X.affineOpens //
    (p.1 : Y.Opens) ≤ ψ ⁻¹ᵁ U ∧ (p.2 : X.Opens) ≤ W ∧ (p.2 : X.Opens) ≤ φ ⁻¹ᵁ (p.1 : Y.Opens)}
  refine BenchOB4.sec_ext ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d) (fun i : ι => (i.1.2 : X.Opens)) W (fun i => i.2.2.1)
    ?_ _ _ ?_
  · intro x hx
    have hx' : φ.base x ∈ (ψ ⁻¹ᵁ U : Y.Opens) := hWU hx
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'U⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx' (ψ ⁻¹ᵁ U).2
    have hx'' : x ∈ (W ⊓ φ ⁻¹ᵁ W' : X.Opens) := ⟨hx, hxW'⟩
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀le⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx'' (W ⊓ φ ⁻¹ᵁ W').2
    exact ⟨⟨⟨⟨W', hW'⟩, ⟨W₀, hW₀⟩⟩, hW'U, fun y hy => (hW₀le hy).1, fun y hy => (hW₀le hy).2⟩, hxW₀⟩
  · rintro ⟨⟨⟨W', hW'⟩, ⟨W₀, hW₀⟩⟩, hW'U, hW₀W, hW₀W'⟩
    have h₀ : W₀ ≤ (φ ≫ ψ) ⁻¹ᵁ U := hW₀W.trans hWU
    have hφW' : φ ⁻¹ᵁ W' ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U) := fun y hy => hW'U hy
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gZ) U; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gY) W'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W₀
    letI : Algebra Γ(Z, U) Γ(Y, W') := (ψ.appLE U W' hW'U).hom.toAlgebra
    letI : Algebra Γ(Y, W') Γ(X, W₀) := (φ.appLE W' W₀ hW₀W').hom.toAlgebra
    letI : Algebra Γ(Z, U) Γ(X, W₀) := ((φ ≫ ψ).appLE U W₀ h₀).hom.toAlgebra
    haveI : IsScalarTower Γ(Z, U) Γ(Y, W') Γ(X, W₀) := IsScalarTower.of_algebraMap_eq' (by
      change ((φ ≫ ψ).appLE U W₀ h₀).hom = (φ.appLE W' W₀ hW₀W').hom.comp (ψ.appLE U W' hW'U).hom
      rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE])
    letI : Algebra A Γ(Y, W') := ((algebraMap Γ(Z, U) Γ(Y, W')).comp (algebraMap A Γ(Z, U))).toAlgebra
    haveI : IsScalarTower A Γ(Z, U) Γ(Y, W') := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower A B Γ(Y, W') :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => BenchOB4.algebraMap_comm gZ gY ψ hψ U W' hW'U a)
    letI : Algebra B Γ(X, W₀) := ((algebraMap Γ(Y, W') Γ(X, W₀)).comp (algebraMap B Γ(Y, W'))).toAlgebra
    haveI : IsScalarTower B Γ(Y, W') Γ(X, W₀) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower B C Γ(X, W₀) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun b => BenchOB4.algebraMap_comm gY gX φ hφ W' W₀ hW₀W' b)
    letI : Algebra A Γ(X, W₀) := ((algebraMap Γ(Z, U) Γ(X, W₀)).comp (algebraMap A Γ(Z, U))).toAlgebra
    haveI : IsScalarTower A Γ(Z, U) Γ(X, W₀) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower A C Γ(X, W₀) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
        BenchOB4.algebraMap_comm gZ gX (φ ≫ ψ) hφψ U W₀ h₀ a)
    conv_rhs =>
      rw [BenchOB4.map_map ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d) (homOfLE hWU) (homOfLE hW₀W) (homOfLE h₀),
        hθ U hU W₀ hW₀ h₀ η]
    have h₀' : W₀ ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U) := hW₀W'.trans hφW'
    rw [BenchOB4.map_map ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d) (homOfLE hWU) (homOfLE hW₀W) (homOfLE h₀)]
    erw [← BenchOB4.map_map ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gX) d) (homOfLE hφW') (homOfLE hW₀W') (homOfLE h₀')]
    rw [BenchOB4.app_naturality θφ (homOfLE hφW'),
      Scheme.Modules.map_homOfLE_pullbackLocalSection φ hW'U,
      hθψ U hU W' hW' hW'U η,
      hθφ W' hW' W₀ hW₀ hW₀W' _]
    rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap]


end P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_pullbackComp_inv_app_comp_map_comp_of_map_pullbackLocalSection_topToSections_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
