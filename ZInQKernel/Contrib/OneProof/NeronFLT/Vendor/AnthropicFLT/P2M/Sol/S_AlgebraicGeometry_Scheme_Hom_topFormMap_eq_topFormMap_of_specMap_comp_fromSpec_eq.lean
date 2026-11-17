/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace BenchOCC

theorem exists_ringHom_of_mem {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) (hφ : φ.base (IsLocalRing.closedPoint F) ∈ U) :
    ∃ ψ : Γ(X, U) →+* F, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = φ := by
  have hr : Set.range φ.base ⊆ Set.range hU.fromSpec.base := by
    rw [IsAffineOpen.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint F)]
    exact hφ
  let θ := IsOpenImmersion.lift hU.fromSpec φ hr
  refine ⟨(Spec.preimage θ).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem ringHom_eq_of_specMap_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [CommRing F] (ψ₁ ψ₂ : Γ(X, U) →+* F)
    (h : Spec.map (CommRingCat.ofHom ψ₁) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom ψ₂) ≫ hU.fromSpec) :
    ψ₁ = ψ₂ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ₁) = Spec.map (CommRingCat.ofHom ψ₂) := (cancel_mono _).mp h
  exact congrArg (fun f => f.hom) (Spec.map_injective h1)

theorem isScalarTower_sections {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {U W : X.Opens} (h : W ≤ U) :
    letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
    letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower A Γ(X, U) Γ(X, W) := by
  letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
  letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have hnat := f.constToPresheaf.naturality (homOfLE h).op

  have := congrArg (fun g => CommRingCat.Hom.hom g) hnat
  simp only [Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp] at this
  exact this

end BenchOCC

theorem solution
    {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(g.topDifferentials d, ⊤))
    (F : Type u) [Field F] [Algebra K F]
    (U₁ : X.Opens) (hU₁ : IsAffineOpen U₁) [Algebra Γ(X, U₁) F]
    (hKU₁ : letI := g.sectionsAlgebra U₁; IsScalarTower K Γ(X, U₁) F)
    (U₂ : X.Opens) (hU₂ : IsAffineOpen U₂) [Algebra Γ(X, U₂) F]
    (hKU₂ : letI := g.sectionsAlgebra U₂; IsScalarTower K Γ(X, U₂) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F)) ≫ hU₁.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₂) F)) ≫ hU₂.fromSpec)
    (ω₁ : ⋀[Γ(X, U₁)]^d (g.kaehlerPresheaf.obj (op U₁)))
    (hω₁ : g.topToSections d U₁ ω₁ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
    (ω₂ : ⋀[Γ(X, U₂)]^d (g.kaehlerPresheaf.obj (op U₂)))
    (hω₂ : g.topToSections d U₂ ω₂ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    letI := g.sectionsAlgebra U₁; letI := g.sectionsAlgebra U₂
    NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₁) F d ω₁ =
      NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₂) F d ω₂ := by
  letI i₁ := g.sectionsAlgebra U₁; letI i₂ := g.sectionsAlgebra U₂

  set x : Spec (CommRingCat.of F) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F)) ≫ hU₁.fromSpec
    with hxdef
  have hp₁ : x.base (IsLocalRing.closedPoint F) ∈ U₁ := by
    have : x.base (IsLocalRing.closedPoint F) ∈ Set.range hU₁.fromSpec.base :=
      ⟨(Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F))).base (IsLocalRing.closedPoint F), by
        rw [hxdef]; rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  have hp₂ : x.base (IsLocalRing.closedPoint F) ∈ U₂ := by
    have : x.base (IsLocalRing.closedPoint F) ∈ Set.range hU₂.fromSpec.base :=
      ⟨(Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₂) F))).base (IsLocalRing.closedPoint F), by
        rw [hx]; rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x.base (IsLocalRing.closedPoint F) ∈ (U₁ ⊓ U₂ : X.Opens)
      from ⟨hp₁, hp₂⟩) (U₁ ⊓ U₂).2
  have hW₁ : W ≤ U₁ := fun y hy => (hWle hy).1
  have hW₂ : W ≤ U₂ := fun y hy => (hWle hy).2
  obtain ⟨ψ, hψ⟩ := BenchOCC.exists_ringHom_of_mem hW x hpW

  have hfac₁ : algebraMap Γ(X, U₁) F = ψ.comp (X.presheaf.map (homOfLE hW₁).op).hom := by
    apply BenchOCC.ringHom_eq_of_specMap_comp_fromSpec hU₁
    rw [← hxdef, ← hψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
      hU₁.map_fromSpec hW]
  have hfac₂ : algebraMap Γ(X, U₂) F = ψ.comp (X.presheaf.map (homOfLE hW₂).op).hom := by
    apply BenchOCC.ringHom_eq_of_specMap_comp_fromSpec hU₂
    rw [← hx, ← hψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
      hU₂.map_fromSpec hW]

  letI iW := g.sectionsAlgebra W
  letI a₁ : Algebra Γ(X, U₁) Γ(X, W) := (X.presheaf.map (homOfLE hW₁).op).hom.toAlgebra
  letI a₂ : Algebra Γ(X, U₂) Γ(X, W) := (X.presheaf.map (homOfLE hW₂).op).hom.toAlgebra
  letI aF : Algebra Γ(X, W) F := ψ.toAlgebra
  haveI t₁ : IsScalarTower K Γ(X, U₁) Γ(X, W) := BenchOCC.isScalarTower_sections g hW₁
  haveI t₂ : IsScalarTower K Γ(X, U₂) Γ(X, W) := BenchOCC.isScalarTower_sections g hW₂
  haveI s₁ : IsScalarTower Γ(X, U₁) Γ(X, W) F := IsScalarTower.of_algebraMap_eq' hfac₁
  haveI s₂ : IsScalarTower Γ(X, U₂) Γ(X, W) F := IsScalarTower.of_algebraMap_eq' hfac₂
  haveI sK : IsScalarTower K Γ(X, W) F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K Γ(X, U₁) F, IsScalarTower.algebraMap_eq Γ(X, U₁) Γ(X, W) F,
      IsScalarTower.algebraMap_eq K Γ(X, U₁) Γ(X, W), RingHom.comp_assoc])

  have hT := Scheme.Hom.topToSections_bijective_of_isAffineOpen g d hW
  have key : NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₁) Γ(X, W) d ω₁ =
      NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₂) Γ(X, W) d ω₂ := by
    apply hT.1
    rw [← Scheme.Hom.map_topToSections_eq_topToSections_topFormMap g d hW₁ ω₁,
      ← Scheme.Hom.map_topToSections_eq_topToSections_topFormMap g d hW₂ ω₂, hω₁, hω₂,
      ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  have e := congrArg (fun s => NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, W) F d s) key
  try dsimp only at e
  rw [NeronModelInfra.TopFormOrder.topFormMap_topFormMap, NeronModelInfra.TopFormOrder.topFormMap_topFormMap] at e
  exact e
