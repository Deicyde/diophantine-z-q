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
  Source file    : P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace.lean
  Source sha256  : 721af75b381991e26e8906992e22f7153f6d80b0719f825d6354f0ceeef8b06a
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
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsSeparated f] [QuasiCompact f] [IrreducibleSpace Y] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsFinite (f ∣_ U) := by
  classical

  let η : Y := genericPoint Y
  obtain ⟨V₀, hV₀, hηV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top η)
  let V : Y.Opens := V₀
  have hV : IsAffineOpen V := hV₀
  have hηV : η ∈ V := hηV
  let e := hV.isoSpec
  let g : (f ⁻¹ᵁ V).toScheme ⟶ Spec (CommRingCat.of Γ(Y, V)) := (f ∣_ V) ≫ e.hom

  let p : PrimeSpectrum Γ(Y, V) := e.hom.base ⟨η, hηV⟩
  have hpmin : p.asIdeal ∈ minimalPrimes Γ(Y, V) := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨p.isPrime, fun q hq hqp => ?_⟩

    let y : V := e.inv.base ⟨q, hq⟩
    have h1 : (⟨η, hηV⟩ : V) ⤳ y := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      exact genericPoint_specializes _
    have h2 : p ⤳ e.hom.base y := h1.map e.hom.continuous
    have h3 : e.hom.base y = ⟨q, hq⟩ := by
      show (e.inv ≫ e.hom).base ⟨q, hq⟩ = _
      rw [e.inv_hom_id]; rfl
    rw [h3, ← PrimeSpectrum.le_iff_specializes] at h2
    exact h2
  haveI : IsSeparated g := inferInstance
  obtain ⟨r, hrp, hfin⟩ :=
    AlgebraicGeometry.LocallyQuasiFinite.exists_not_mem_isFinite_morphismRestrict_basicOpen_of_mem_minimalPrimes
      g p.asIdeal hpmin

  let W : V.toScheme.Opens := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  refine ⟨V.ι ''ᵁ W, ⟨η, ?_⟩, ?_⟩
  · refine ⟨⟨η, hηV⟩, ?_, rfl⟩
    show p ∈ PrimeSpectrum.basicOpen r
    exact hrp
  ·
    have h1 : IsFinite ((f ∣_ V) ∣_ W) := by
      have hc : g ∣_ PrimeSpectrum.basicOpen r = ((f ∣_ V) ∣_ W) ≫ (e.hom ∣_ PrimeSpectrum.basicOpen r) :=
        morphismRestrict_comp _ _ _
      rw [hc] at hfin
      exact (MorphismProperty.cancel_right_of_respectsIso @IsFinite ((f ∣_ V) ∣_ W)
        (e.hom ∣_ PrimeSpectrum.basicOpen r)).mp hfin
    exact ((MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f V W)).mp h1)
end S_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
