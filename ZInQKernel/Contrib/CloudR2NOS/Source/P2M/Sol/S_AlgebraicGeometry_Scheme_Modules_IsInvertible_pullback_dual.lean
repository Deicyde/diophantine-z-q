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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual.lean
  Source sha256  : ecfc641566021a829f500ae80bb3b5fbe61f61907fd2ede711ec78b4f8fbbd95
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_PullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible.dual"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules Modules.IsInvertible Modules.dual Modules.pullbackTensorUnitObjIso Modules.IsInvertible.dual"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "pullback IsInvertible dual pullbackTensorUnitObjIso IsInvertible.dual"
namespace InverseUnique
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

w03_open "CategoryTheory CategoryTheory.MonoidalCategory"

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique" in
theorem solution {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.dual L) ≅
      AlgebraicGeometry.Scheme.Modules.dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)) := by
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual hL).2
  obtain ⟨e'⟩ := (Scheme.Modules.IsInvertible.dual (hL.pullback f)).2

  let e : (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj (Scheme.Modules.dual L) ≅
      𝟙_ X.Modules :=
    Functor.Monoidal.μIso (Scheme.Modules.pullback f) L (Scheme.Modules.dual L) ≪≫
      (Scheme.Modules.pullback f).mapIso eL ≪≫ Scheme.Modules.pullbackTensorUnitObjIso f
  exact ⟨inverseUnique e e'⟩
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
