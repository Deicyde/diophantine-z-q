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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible.lean
  Source sha256  : d5dbfe31723063410b89a54ec1f424b3ec9bf01633a71c991b3860d7ee464b70
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

namespace C2E5
r2nos_namespace_dual

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).subscheme := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI

  haveI : IrreducibleSpace I.subscheme := by
    have h : IsIrreducible ((I.support : TopologicalSpace.Closeds X) : Set X) := by
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hZ'
    exact Subtype.irreducibleSpace h

  have hred : ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) := fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced, hI, Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    haveI := hred U
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, U.1) ⧸ I.ideal U))))
  haveI : IsReduced I.subscheme := IsReduced.of_openCover (X := I.subscheme) I.subschemeCover.openCover
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible.solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z) (U : X.Opens) (hZU : Z ⊆ U) (g : Γ(X, U)) :
    Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩ with hI
  haveI : IsIntegral I.subscheme := isIntegral_subscheme_vanishingIdeal Z hZ hZ'

  have hrange : Set.range I.subschemeι.base = Z := by
    change Set.range I.subschemeι = Z
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl

  haveI : UniversallyClosed (I.subschemeι ≫ t) := inferInstance
  have hF : IsField Γ(I.subscheme, ⊤) := isField_of_universallyClosed k (I.subschemeι ≫ t)

  have hpre : I.subschemeι ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    show I.subschemeι.base z ∈ U
    exact hZU (hrange ▸ Set.mem_range_self z)
  have hF' : IsField Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) := by rw [hpre]; exact hF
  letI := hF'.toField

  have key : I.subschemeι ⁻¹ᵁ X.basicOpen g = I.subscheme.basicOpen (I.subschemeι.app U g) :=
    Scheme.preimage_basicOpen I.subschemeι g
  by_cases h0 : I.subschemeι.app U g = 0
  · right
    rw [Set.disjoint_left]
    rintro z hz hzg
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    have : z' ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g := hzg
    rw [key, h0, Scheme.basicOpen_zero] at this
    exact this
  · left
    intro z hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range I.subschemeι.base := hrange ▸ hz
    show z' ∈ I.subschemeι ⁻¹ᵁ X.basicOpen g
    rw [key, I.subscheme.basicOpen_of_isUnit (isUnit_iff_ne_zero.mpr h0), hpre]
    trivial

end C2E5
end S_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
