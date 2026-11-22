/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

def projectionMorphismMate (F : X.Modules) :
    (Modules.pullback i).obj ((Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F) ⟶ (Modules.pullback i).obj F :=
  (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
    ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
    (λ_ ((Modules.pullback i).obj F)).hom

def projectionMorphism (F : X.Modules) :
    (Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F ⟶ (Modules.pushforward i).obj ((Modules.pullback i).obj F) :=
  ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F)

theorem projectionMorphism_def (F : X.Modules) :
    projectionMorphism i F = ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F) := rfl

theorem projectionMorphismMate_def (F : X.Modules) :
    projectionMorphismMate i F =
      (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
        ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
        (λ_ ((Modules.pullback i).obj F)).hom := rfl

end AlgebraicGeometry.Scheme.Modules

end
