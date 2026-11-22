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
  Source file    : P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf.lean
  Source sha256  : aae522e905fee8dbc61ab9cd0538e85c0979aacf5dacbbe779d0ee1ef00fa538
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`.
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

namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

universe u

theorem solution
    {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  set A := Γ(X, U) with hA
  set F := X.functionField with hF
  haveI : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  apply le_antisymm
  ·
    refine le_iInf₂ fun x hx => ?_
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    haveI : IsScalarTower A (X.presheaf.stalk x) F := functionField_isScalarTower X U ⟨x, hx⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap A (X.presheaf.stalk x) a, (IsScalarTower.algebraMap_apply A _ F a).symm⟩
  ·
    intro f hf
    have key : f ∈ (⨅ v : PrimeSpectrum A,
        Localization.subalgebra.ofField F _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
      refine Algebra.mem_iInf.mpr fun v => ?_

      have hxU : (hU.fromSpec v : X) ∈ U := by
        show (hU.fromSpec v : X) ∈ (U : Set X)
        rw [← hU.range_fromSpec]
        exact ⟨v, rfl⟩
      letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec v, hxU⟩ : U)
      haveI : IsScalarTower A (X.presheaf.stalk (hU.fromSpec v : X)) F :=
        functionField_isScalarTower X U ⟨_, hxU⟩
      haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec v : X)) v.asIdeal :=
        hU.isLocalization_stalk' v hxU
      have hfx : f ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec v : X)) F).range :=
        (Subring.mem_iInf.mp ((Subring.mem_iInf.mp hf) (hU.fromSpec v : X))) hxU
      obtain ⟨s, rfl⟩ := hfx
      obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl s
      refine ⟨a, t, t.2, ?_⟩
      have ht : algebraMap A F t ≠ 0 := by
        intro h0
        have : (t : A) = 0 := (IsFractionRing.injective A F) (by rw [h0, map_zero])
        exact t.2 (by rw [this]; exact v.asIdeal.zero_mem)
      rw [eq_mul_inv_iff_mul_eq₀ ht,
        IsScalarTower.algebraMap_apply A (X.presheaf.stalk (hU.fromSpec v : X)) F (t : A),
        ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply A (X.presheaf.stalk (hU.fromSpec v : X)) F a]
    rw [PrimeSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at key
    obtain ⟨a, rfl⟩ := key
    exact ⟨a, rfl⟩
end S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
