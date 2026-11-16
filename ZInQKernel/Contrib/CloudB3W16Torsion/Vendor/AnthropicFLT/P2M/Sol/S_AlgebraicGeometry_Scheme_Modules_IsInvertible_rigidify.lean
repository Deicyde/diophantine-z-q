/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

theorem solution
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (Scheme.Modules.rigidify σ q L) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj (Scheme.Modules.rigidify σ q L) ≅ 𝟙_ T.Modules) := by

  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨hM, ⟨pairing⟩⟩ := Scheme.Modules.IsInvertible.dual hσL
  refine ⟨hL.tensor (Scheme.Modules.IsInvertible.pullback q hM), ⟨?_⟩⟩
  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)

  let e : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp σ q).app M ≪≫
      (Scheme.Modules.pullbackCongr hσq).app M ≪≫ (Scheme.Modules.pullbackId (X := T)).app M
  exact Scheme.Modules.pullbackTensorObjIso σ L _ ≪≫ (Iso.refl _ ⊗ᵢ e) ≪≫ pairing
