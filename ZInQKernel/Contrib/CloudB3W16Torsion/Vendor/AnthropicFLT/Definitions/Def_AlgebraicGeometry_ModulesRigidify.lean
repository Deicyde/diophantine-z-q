/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_ModulesRigidify. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T P : Scheme.{u}}

def dualMapIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

def rigidify (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) : P.Modules :=
  L ⊗ (Scheme.Modules.pullback q).obj
    (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))

lemma rigidify_def (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) :
    rigidify σ q L = L ⊗ (Scheme.Modules.pullback q).obj
      (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) := rfl

def rigidifyMapIso (σ : T ⟶ P) (q : P ⟶ T) {L L' : P.Modules} (e : L ≅ L') :
    rigidify σ q L ≅ rigidify σ q L' :=
  e ⊗ᵢ (Scheme.Modules.pullback q).mapIso (dualMapIso ((Scheme.Modules.pullback σ).mapIso e))

end AlgebraicGeometry.Scheme.Modules

end
