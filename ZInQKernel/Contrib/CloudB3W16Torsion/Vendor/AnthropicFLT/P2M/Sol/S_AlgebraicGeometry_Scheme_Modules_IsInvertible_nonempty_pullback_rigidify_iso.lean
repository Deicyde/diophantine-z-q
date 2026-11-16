/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

theorem solution
    {T P T' P' : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} {σ' : T' ⟶ P'} {q' : P' ⟶ T'}
    (ψ : T' ⟶ T) (Ψ : P' ⟶ P) (hσ : σ' ≫ Ψ = ψ ≫ σ) (hq : Ψ ≫ q = q' ≫ ψ)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback Ψ).obj (Scheme.Modules.rigidify σ q L) ≅
      Scheme.Modules.rigidify σ' q' ((Scheme.Modules.pullback Ψ).obj L)) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨d⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ hσL

  let e₁ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback σ).obj L) ≅
      (Scheme.Modules.pullback σ').obj ((Scheme.Modules.pullback Ψ).obj L) :=
    (Scheme.Modules.pullbackComp ψ σ).app L ≪≫ (Scheme.Modules.pullbackCongr hσ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp σ' Ψ).app L).symm

  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)
  let e₂ : (Scheme.Modules.pullback Ψ).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback ψ).obj M) :=
    (Scheme.Modules.pullbackComp Ψ q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
      ((Scheme.Modules.pullbackComp q' ψ).app M).symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso Ψ L _ ≪≫
    (Iso.refl _ ⊗ᵢ (e₂ ≪≫ (Scheme.Modules.pullback q').mapIso
      (d ≪≫ Scheme.Modules.dualMapIso e₁)))⟩
