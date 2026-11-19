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
  Source file    : P2M/Sol/S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field.lean
  Source sha256  : 4c3c5af2ddf53ba509bb960c49b637e2150f708c361fa72287b9ef99a1f57508
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "SmoothOfRelativeDimension LocallyQuasiFinite IsFinite QuasiCompact LocallyOfFiniteType Spec Scheme IsLocallyArtinian HasRingHomProperty.appLE Etale HasRingHomProperty.iff_appLE Scheme.isLocallyArtinianScheme_Spec FormallyUnramified HasRingHomProperty IsFinite.of_locallyQuasiFinite Etale.iff_smoothOfRelativeDimension_zero"
namespace EtaleOverField
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ : RingHom.FormallyUnramified (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) f inferInstance U V e
  have h₂ : RingHom.FiniteType (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  rw [RingHom.QuasiFinite]
  have : Algebra.EssFiniteType Γ(Y, U) Γ(X, V) :=
    Algebra.EssFiniteType.of_finiteType _ _
  infer_instance

theorem isFinite_of_etale {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Etale f] [QuasiCompact f] : IsFinite f := by
  have hlqf : LocallyQuasiFinite f := locallyQuasiFinite_of_formallyUnramified f
  have hArt : IsLocallyArtinian (Spec (CommRingCat.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr (inferInstanceAs (IsArtinianRing k))
  exact IsFinite.of_locallyQuasiFinite f

end AlgebraicGeometry.EtaleOverField

open AlgebraicGeometry.EtaleOverField in
r2nos_open_dual "AlgebraicGeometry.EtaleOverField" in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 0 f] [QuasiCompact f] : IsFinite f := by
  have hEt : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
  exact isFinite_of_etale f
end S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
