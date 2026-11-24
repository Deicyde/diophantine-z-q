/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace P2mGeoMumfordModel

theorem isEmpty_idx {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι < i + 1) :
    IsEmpty (𝒰.Idx i) := by
  refine ⟨fun s => ?_⟩
  have h := Fintype.card_le_of_injective s.1 s.2.injective
  rw [Fintype.card_fin] at h
  omega

theorem subsingleton_cochain {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (𝒰 : X.OrderedAffineCover) (i : ℕ) (hi : Fintype.card 𝒰.ι < i) :
    Subsingleton (F.cochain 𝒰 i) := by
  haveI : IsEmpty (𝒰.Idx i) := isEmpty_idx 𝒰 i (by omega)
  change Subsingleton (∀ s : 𝒰.Idx i, F.obj (𝒰.inter s))
  infer_instance

theorem main
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ι0 : G.C0 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 0)
      (ι1 : G.C1 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 1)
      (comm : (OModulePresheaf.ofModules f M).d 𝒰 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective
          (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm A) := by
  set F := OModulePresheaf.ofModules f M with hF
  haveI : ∀ i, Module.Flat R (F.cochain 𝒰 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f M htriv 𝒰 i
  have hdd : ∀ i, F.d 𝒰 (i + 1) ∘ₗ F.d 𝒰 i = 0 := fun i => OModulePresheaf.d_comp_d F 𝒰 i
  have hbdd : ∀ i, Fintype.card 𝒰.ι < i → Subsingleton (F.cochain 𝒰 i) :=
    fun i hi => subsingleton_cochain F 𝒰 i hi
  have hCF : F.CechFinite 𝒰 := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M htriv 𝒰
  exact Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex R
    (fun i => F.cochain 𝒰 i) (fun i => F.d 𝒰 i) hdd (Fintype.card 𝒰.ι) hbdd hCF.1 hCF.2

end P2mGeoMumfordModel

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ι0 : G.C0 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 0)
      (ι1 : G.C1 →ₗ[R] (OModulePresheaf.ofModules f M).cochain 𝒰 1)
      (comm : (OModulePresheaf.ofModules f M).d 𝒰 0 ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective
          (TwoChartCech.kerMapBaseChange G.d ((OModulePresheaf.ofModules f M).d 𝒰 0) ι0 ι1 comm A) :=
  P2mGeoMumfordModel.main f M htriv 𝒰
