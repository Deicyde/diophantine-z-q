/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.lean
  Source sha256  : 8e1b7ef5c4c8ad0e4b99b5691e90c0b1d0cfbce038bba54606853d72c22aa852
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

/-
DEFAULT-LIMIT RE-PROOF EDITION 1, exclusively assigned by H5 C4 to H4 L5.
The attribution and port history above are retained verbatim from base873e12c0.
New modification: factor the original affine-section argument into explicit
inclusion/projection maps and two finite-section lemmas. The original theorem
and solution names/statements/imports are unchanged, including every k.
No numeric set_option, admission, new import, or native invocation.
Only permitted backward.isDefEq.respectTransparency.types/instanceSearchTypes
false switches are retained. Both autoImplicit false switches from the base
are removed; autoImplicit and all limits are left at registered defaults.
SOURCE CANDIDATE ONLY; parent probes and C4 binding determine acceptance.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsLocallyNoetherian Spec Scheme IsLocallyNoetherian.component_noetherian IsNoetherian OModulePresheaf.idealPowQuot OModulePresheaf OModulePresheaf.IsCoherent Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "idealPowSub idealPow idealPowSuccSub idealPowQuot_smul_mk idealPowQuot IsCoherent isScalarTower obj"
namespace G4T
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section Closure

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

/-- The actual ideal-power section inclusion, linear over the SAME section ring.
It is constructed once, rather than synthesized inside the coherence proof. -/
def idealPowSubtypeGamma (I : V.IdealSheafData) (F : OModulePresheaf π)
    (k : ℕ) (U : V.Opens) :
    (idealPow π I F k).obj U →ₗ[Γ(V, U)] F.obj U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule
  haveI := F.isScalarTower U
  exact
    { toFun := fun x => x.1
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }

/-- The literal quotient projection, linear for the GIVEN quotient-section
module structure. No abstract replacement quotient or surjectivity input. -/
def idealPowQuotMkGamma (I : V.IdealSheafData) (F : OModulePresheaf π)
    (k : ℕ) (U : V.Opens) :
    (idealPow π I F k).obj U →ₗ[Γ(V, U)] (idealPowQuot π I F k).obj U := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule
  haveI := F.isScalarTower U
  exact
    { toFun := (idealPowSuccSub π I F k U).mkQ
      map_add' := map_add _
      map_smul' := fun a y => (idealPowQuot_smul_mk π I F k U a y).symm }

/-- An ideal-power section module is finite because it embeds into the
original finite section module over its Noetherian affine section ring. -/
theorem finite_idealPow_sections [IsLocallyNoetherian V] (I : V.IdealSheafData)
    (F : OModulePresheaf π) (k : ℕ) (hFc : OModulePresheaf.IsCoherent F)
    (U : V.affineOpens) : Module.Finite Γ(V, U.1) ((idealPow π I F k).obj U.1) := by
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := hFc U
  haveI : _root_.IsNoetherian (Γ(V, U.1)) (F.obj U.1) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective (idealPowSubtypeGamma π I F k U.1)
    (fun x y h => Subtype.ext h)

/-- The actual quotient is finite by its actual surjective section map.
The finite ideal-power source is a proved helper, not a new hypothesis. -/
theorem finite_idealPowQuot_sections [IsLocallyNoetherian V] (I : V.IdealSheafData)
    (F : OModulePresheaf π) (k : ℕ) (hFc : OModulePresheaf.IsCoherent F)
    (U : V.affineOpens) : Module.Finite Γ(V, U.1) ((idealPowQuot π I F k).obj U.1) := by
  haveI := finite_idealPow_sections π I F k hFc U
  exact Module.Finite.of_surjective (idealPowQuotMkGamma π I F k U.1)
    (Submodule.mkQ_surjective (idealPowSuccSub π I F k U.1))

theorem isCoherent_idealPowQuot [IsLocallyNoetherian V] (I : V.IdealSheafData)
    (F : OModulePresheaf π) (k : ℕ) (hFc : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (idealPowQuot π I F k) := fun U =>
  finite_idealPowQuot_sections π I F k hFc U

end Closure

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.AlgebraicGeometry" in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (hFc : F.IsCoherent) : (OModulePresheaf.idealPowQuot π I F k).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_idealPowQuot π I F k hFc
end S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
