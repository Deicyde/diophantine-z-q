/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesProjectionMorphism.lean
  Source sha256  : b54f56fba4f2dc37f677bc19f71687fbd8c7aa4051bd34d4d45a4c347577881b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-6 (lane4) T10×1: a multi-token `open A B …` whose relative token (MonoidalCategory) is resolved after `A` has opened only the port's prefixed twin ("unknown namespace", a Parent compile probe) is split into one `open` + dual shim per token, so each token sees the root half opened by the previous shim (source semantics).
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory
r2nos_open_dual "CategoryTheory"
open MonoidalCategory
r2nos_open_dual "MonoidalCategory"

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules
r2nos_namespace_dual

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

end ZInQ.Contrib.CloudW03NeronSurj.FLT
