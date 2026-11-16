/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

def lbTB_tensorExchange {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V]
    (A B C D : V) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ (Iso.refl A ⊗ᵢ ((α_ B C D).symm ≪≫ (β_ B C ⊗ᵢ Iso.refl D) ≪≫ α_ C B D)) ≪≫
    (α_ A C (B ⊗ D)).symm

theorem solution
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q ((Scheme.Modules.pullback q).obj N ⊗ L) ≅
      Scheme.Modules.rigidify σ q L) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨_, ⟨pairN⟩⟩ := Scheme.Modules.IsInvertible.dual hN
  obtain ⟨dt⟩ := Scheme.Modules.IsInvertible.dual_tensor hN hσL

  let eN : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj N) ≅ N :=
    (Scheme.Modules.pullbackComp σ q).app N ≪≫ (Scheme.Modules.pullbackCongr hσq).app N ≪≫
      (Scheme.Modules.pullbackId (X := T)).app N

  let eD : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj
      ((Scheme.Modules.pullback q).obj N ⊗ L)) ≅
      Scheme.Modules.dual N ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ (eN ⊗ᵢ Iso.refl _)) ≪≫
      dt

  let eU : (Scheme.Modules.pullback q).obj N ⊗
      (Scheme.Modules.pullback q).obj (Scheme.Modules.dual N) ≅ 𝟙_ P.Modules :=
    (Scheme.Modules.pullbackTensorObjIso q N _).symm ≪≫ (Scheme.Modules.pullback q).mapIso pairN ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q
  refine ⟨?_⟩
  change ((Scheme.Modules.pullback q).obj N ⊗ L) ⊗ (Scheme.Modules.pullback q).obj _ ≅
    L ⊗ (Scheme.Modules.pullback q).obj _
  exact (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso eD ≪≫
      Scheme.Modules.pullbackTensorObjIso q _ _)) ≪≫
    lbTB_tensorExchange _ _ _ _ ≪≫ (eU ⊗ᵢ Iso.refl _) ≪≫ λ_ _
