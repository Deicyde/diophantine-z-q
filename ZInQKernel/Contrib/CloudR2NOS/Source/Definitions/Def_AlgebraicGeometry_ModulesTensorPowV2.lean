/-
NEW SOURCE EDITION — GM12 binding preparation, not historical byte recovery.

Original source: anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicGeometry_ModulesTensorPowV2.lean.
Copyright 2026 Anthropic, PBC; Apache-2.0 (original LICENSE/ATTRIBUTION kept).
Actual original source SHA256:
3914fb3db6d25328f177be556dbe32bcf58a950a666edc272fc3601f92e9ad09.

NOTICE OF MODIFICATION: only the documented namespace-prefix/import port
transform is applied, including its dual namespace/open shims and utility
import. No definition, binder, universe, recursion equation, instance or
proof is edited, and no numeric budget is added. The historical recorded
port SHA15b219dd... is a comparison anchor, not a source-body recipe.
This edition has its own actual bytes and must receive C6 Source review.
No native, Type0 closure port, admission or Source/W07 alias is claimed.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_MonoidalV2
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory
r2nos_open_dual "CategoryTheory MonoidalCategory"

namespace AlgebraicGeometry.Scheme.Modules
r2nos_namespace_dual

variable {X : Scheme.{u}}

def tensorPow (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPow L n ⊗ L

@[simp] theorem tensorPow_zero (L : X.Modules) : L.tensorPow 0 = 𝟙_ X.Modules := rfl

@[simp] theorem tensorPow_succ (L : X.Modules) (n : ℕ) : L.tensorPow (n + 1) = L.tensorPow n ⊗ L := rfl

def tensorPowOneIso (L : X.Modules) : L.tensorPow 1 ≅ L := λ_ L

end AlgebraicGeometry.Scheme.Modules

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
