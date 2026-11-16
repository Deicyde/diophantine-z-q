/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 800000 in
open AlgebraicGeometry Opposite in

theorem solution {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range (I.moduleι.app U) = (I.ideal U : Set Γ(X, U)) ∧
      Function.Injective (I.moduleι.app U) := by

  let R := X.ringCatSheaf
  let F := I.subschemeι.unitToPushforwardUnit

  let G : SheafOfModules R ⥤ ModuleCat (R.obj.obj (op (U : X.Opens))) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op (U : X.Opens))
  haveI : G.Additive := inferInstance
  haveI : PreservesLimit (parallelPair F 0) G := inferInstance
  let e₁ : G.obj (kernel F) ≅ kernel (G.map F) := PreservesKernel.iso G F
  let e₂ : kernel (G.map F) ≅ ModuleCat.of _ (LinearMap.ker (G.map F).hom) :=
    ModuleCat.kernelIsoKer (G.map F)
  have key : G.map (kernel.ι F) =
      e₁.hom ≫ e₂.hom ≫ ModuleCat.ofHom (LinearMap.ker (G.map F).hom).subtype := by
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom, kernelComparison_comp_ι]

  have hfun : ⇑(I.moduleι.app U) = Subtype.val ∘ ⇑(e₁ ≪≫ e₂).toLinearEquiv := by
    funext m
    change (G.map (kernel.ι F)).hom m = _
    rw [key]
    rfl
  have hbij : Function.Bijective ⇑(e₁ ≪≫ e₂).toLinearEquiv := (e₁ ≪≫ e₂).toLinearEquiv.bijective

  have hker : ∀ s, s ∈ LinearMap.ker (G.map F).hom ↔ s ∈ (I.ideal U : Set Γ(X, U)) := fun s ↦ by
    have h1 : s ∈ LinearMap.ker (G.map F).hom ↔ (I.subschemeι.app U).hom s = 0 :=
      LinearMap.mem_ker.trans Iff.rfl
    have h2 : s ∈ (I.ideal U : Set Γ(X, U)) ↔ (I.subschemeι.app U).hom s = 0 := by
      rw [← I.ker_subschemeι_app U]
      exact RingHom.mem_ker
    exact h1.trans h2.symm
  refine ⟨?_, ?_⟩
  · rw [hfun]
    ext s
    constructor
    · rintro ⟨m, rfl⟩
      exact (hker _).mp ((e₁ ≪≫ e₂).toLinearEquiv m).2
    · intro hs
      obtain ⟨m, hm⟩ := hbij.surjective ⟨s, (hker s).mpr hs⟩
      exact ⟨m, by simp [hm]⟩
  · rw [hfun]
    exact Subtype.val_injective.comp hbij.injective
