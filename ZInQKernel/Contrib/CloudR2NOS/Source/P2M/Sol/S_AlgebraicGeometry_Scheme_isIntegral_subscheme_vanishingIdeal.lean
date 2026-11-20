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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean
  Source sha256  : 6040ac51b3aba485bd96f1d530afba5447b2f776da1e8890b1d6bb67deb55ad0
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
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
r2nos_namespace_dual

set_option autoImplicit false
w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry CategoryTheory TopologicalSpace AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry.Scheme"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "affine_isReduced_iff Spec IsIntegral Scheme Scheme.IdealSheafData.vanishingIdeal IsReduced.of_openCover IsReduced Scheme.IdealSheafData isIntegral_of_irreducibleSpace_of_isReduced"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "IdealSheafData.coe_support_vanishingIdeal Γ IdealSheafData.vanishingIdeal IdealSheafData.vanishingIdeal_ideal affineOpens IdealSheafData"
namespace IntegralSubscheme
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme AlgebraicGeometry"
universe u
section IntegralSubscheme

variable {V : Scheme.{u}}

theorem isReduced_vanishingIdeal (Z : Closeds V) :
    IsReduced (IdealSheafData.vanishingIdeal Z).subscheme := by

  have hchart : ∀ U : V.affineOpens,
      IsReduced ((IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) := by
    intro U

    show IsReduced (Spec (CommRingCat.of
      (Γ(V, U.1) ⧸ (IdealSheafData.vanishingIdeal Z).ideal U)))
    rw [affine_isReduced_iff]

    have hrad : ((IdealSheafData.vanishingIdeal Z).ideal U).IsRadical := by
      rw [IdealSheafData.vanishingIdeal_ideal]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨n, hn⟩ := hx
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrad ⟨n, hn⟩)
  haveI := hchart
  exact AlgebraicGeometry.IsReduced.of_openCover
    (X := (IdealSheafData.vanishingIdeal Z).subscheme)
    (IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

theorem support_vanishingIdeal (Z : Closeds V) :
    (IdealSheafData.vanishingIdeal Z).support = Z := by
  exact SetLike.coe_injective (IdealSheafData.coe_support_vanishingIdeal Z)

theorem irreducible_vanishingIdeal (Z : Closeds V)
    (hZ : IsIrreducible (Z : Set V)) :
    IrreducibleSpace (IdealSheafData.vanishingIdeal Z).subscheme := by

  exact Subtype.irreducibleSpace hZ

theorem isIntegral_vanishingIdeal (Z : Closeds V)
    (hZ : IsIrreducible (Z : Set V)) :
    IsIntegral (IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI := isReduced_vanishingIdeal Z
  haveI := irreducible_vanishingIdeal Z hZ
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end IntegralSubscheme
end AlgebraicGeometry.Scheme.IntegralSubscheme

universe u
open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry TopologicalSpace in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.AlgebraicGeometry TopologicalSpace" in
theorem solution {V : Scheme.{u}} (Z : Closeds V) (hZ : IsIrreducible (Z : Set V)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  AlgebraicGeometry.Scheme.IntegralSubscheme.isIntegral_vanishingIdeal Z hZ
end S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
