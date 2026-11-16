/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

def tensorPow (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPow L n ⊗ L

@[simp] theorem tensorPow_zero (L : X.Modules) : L.tensorPow 0 = 𝟙_ X.Modules := rfl

@[simp] theorem tensorPow_succ (L : X.Modules) (n : ℕ) : L.tensorPow (n + 1) = L.tensorPow n ⊗ L := rfl

def tensorPowOneIso (L : X.Modules) : L.tensorPow 1 ≅ L := λ_ L

end AlgebraicGeometry.Scheme.Modules

end
