/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

theorem solution
    {Z X : Scheme.{u}} (i : Z ⟶ X) {F F' : X.Modules} (φ : F ⟶ F') :
    Scheme.Modules.projectionMorphism i F ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) =
      ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫ Scheme.Modules.projectionMorphism i F' := by

  have hmate : Scheme.Modules.projectionMorphismMate i F ≫ (Scheme.Modules.pullback i).map φ =
      (Scheme.Modules.pullback i).map ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫
        Scheme.Modules.projectionMorphismMate i F' := by
    rw [Scheme.Modules.projectionMorphismMate_def, Scheme.Modules.projectionMorphismMate_def,
      Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv]
    simp only [Category.assoc]

    have s1 : ∀ {M M' : Z.Modules} (ψ : M ⟶ M') (W : Z.Modules) (c : W ⟶ 𝟙_ Z.Modules),
        c ▷ M ≫ (λ_ M).hom ≫ ψ = W ◁ ψ ≫ c ▷ M' ≫ (λ_ M').hom := by
      intro M M' ψ W c
      exact ((MonoidalCategory.whisker_exchange_assoc c ψ (λ_ M').hom).symm ▸
        congrArg (fun t => c ▷ M ≫ t) (MonoidalCategory.leftUnitor_naturality ψ).symm :)
    exact (congrArg (fun t => Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) _ _ ≫ t) (s1 _ _ _)).trans
      (Functor.OplaxMonoidal.δ_natural_right_assoc (Scheme.Modules.pullback i) _ φ _)

  have e1 := Adjunction.homEquiv_naturality_right (Scheme.Modules.pullbackPushforwardAdjunction i)
    (Scheme.Modules.projectionMorphismMate i F) ((Scheme.Modules.pullback i).map φ)
  have e2 := Adjunction.homEquiv_naturality_left (Scheme.Modules.pullbackPushforwardAdjunction i)
    ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) (Scheme.Modules.projectionMorphismMate i F')
  exact e1.symm.trans ((congrArg _ hmate).trans e2)
