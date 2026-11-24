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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open.lean
  Source sha256  : c194065994b053ddf839f52f12b84d8eeda1e9fb272d564f8b7e38cfcfbb781d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T6×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_PullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
r2nos_namespace_dual

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme _root_.AlgebraicGeometry in
r2nos_open_dual "CategoryTheory _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme" in

theorem solution
    {Y T : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ T) (V : T.Opens) (L : Y.Modules) (N : T.Modules)
    (eN : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : AlgebraicGeometry.Scheme.{u}).Modules)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj
        (L ⊗ (AlgebraicGeometry.Scheme.Modules.pullback q).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj L) := by
  have hfact : (q ⁻¹ᵁ V).ι ≫ q = (q ∣_ V) ≫ V.ι := (morphismRestrict_ι q V).symm
  refine ⟨Scheme.Modules.pullbackTensorObjIso (q ⁻¹ᵁ V).ι L _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp (q ⁻¹ᵁ V).ι q).app N ≪≫
    (Scheme.Modules.pullbackCongr hfact).app N ≪≫
    ((Scheme.Modules.pullbackComp (q ∣_ V) V.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (q ∣_ V)).mapIso eN ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (q ∣_ V)
end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
