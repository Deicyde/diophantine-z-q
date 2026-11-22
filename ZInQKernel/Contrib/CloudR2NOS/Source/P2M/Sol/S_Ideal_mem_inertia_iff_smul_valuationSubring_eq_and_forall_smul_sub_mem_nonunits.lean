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
  Source file    : P2M/Sol/S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits.lean
  Source sha256  : 6895e96de79f713b6fb16c37354baab0e42d535899aa98994f593749b3c49592
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
r2nos_namespace_dual

set_option autoImplicit false

open scoped Pointwise
r2nos_open_scoped_dual "Pointwise"

theorem solution
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) :
    g ∈ 𝔶.inertia G ↔ (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) := by

  have hnu : ∀ (h : G) (x : F), x ∈ (h • P).nonunits ↔ h⁻¹ • x ∈ P.nonunits := by
    intro h x
    simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      smul_inv'', smul_eq_zero_iff_eq]

  have hmem : ∀ {h : G}, h ∈ 𝔶.inertia G → ∀ b : B, h • b ∈ 𝔶 ↔ b ∈ 𝔶 := by
    intro h hh b
    have hb := hh b
    constructor
    · intro h1; simpa using 𝔶.sub_mem h1 hb
    · intro h1; simpa using 𝔶.add_mem hb h1
  constructor
  · intro hg

    have hstab : g • P = P := by
      apply huniq
      · intro b
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hρ]
        exact hP _
      · intro b
        rw [hnu, hρ, hPy]
        exact hmem (inv_mem hg) b
    refine ⟨hstab, fun e => ?_⟩

    obtain ⟨b, hb⟩ := hres e
    have h1 : g • ((e : F) - ρ b) ∈ P.nonunits := by
      have : g • ((e : F) - ρ b) ∈ (g • P).nonunits := by
        rw [hnu, inv_smul_smul]; exact hb
      rwa [hstab] at this
    have h2 : g • ρ b - ρ b ∈ P.nonunits := by
      rw [hρ, ← map_sub]; exact (hPy _).mpr (hg b)
    have h3 : ρ b - (e : F) ∈ P.nonunits := by
      have := P.nonunits.neg_mem hb
      rwa [neg_sub] at this
    have : g • (e : F) - e = g • ((e : F) - ρ b) + (g • ρ b - ρ b) + (ρ b - e) := by
      rw [smul_sub]; ring
    rw [this]
    exact P.nonunits.add_mem (P.nonunits.add_mem h1 h2) h3
  · rintro ⟨-, hres'⟩ b
    have h := hres' ⟨ρ b, hP b⟩
    change g • ρ b - ρ b ∈ P.nonunits at h
    rw [hρ, ← map_sub] at h
    exact (hPy _).mp h
end S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
