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

def tensorPowFLT (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPowFLT L n ⊗ L

@[simp] theorem tensorPow_zeroFLT (L : X.Modules) : L.tensorPowFLT 0 = 𝟙_ X.Modules := rfl

@[simp] theorem tensorPow_succFLT (L : X.Modules) (n : ℕ) : L.tensorPowFLT (n + 1) = L.tensorPowFLT n ⊗ L := rfl

def tensorPowOneIsoFLT (L : X.Modules) : L.tensorPowFLT 1 ≅ L := λ_ L

end AlgebraicGeometry.Scheme.Modules

end
