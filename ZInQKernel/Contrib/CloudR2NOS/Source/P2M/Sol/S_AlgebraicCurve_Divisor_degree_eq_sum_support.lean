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
  Source file    : P2M/Sol/S_AlgebraicCurve_Divisor_degree_eq_sum_support.lean
  Source sha256  : e87ce795171b5468dce9234392946cbdfe3ce5b2018a60c03848aa327f569d9f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 11 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 3200000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum_support
r2nos_namespace_dual

set_option autoImplicit false

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver LSpace ell mem_lSpace_iff_ord WeilDifferentialRankOne StichtenothGenusExists"
w03_open "AlgebraicCurve"
namespace Place
r2nos_namespace_dual
w03_export "AlgebraicCurve.Place" "deg ord ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring"
w03_open "AlgebraicCurve.Place"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
w03_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
w03_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver LSpace ell mem_lSpace_iff_ord WeilDifferentialRankOne StichtenothGenusExists"
w03_open "AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
namespace Divisor
r2nos_namespace_dual
w03_export "AlgebraicCurve.Divisor" "degree"
end Divisor
r2nos_open_scoped "AlgebraicCurve.Divisor" in
theorem Divisor.degree_eq_sum_support_port (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl
variable {D : Divisor K F}
r2nos_open_scoped "AlgebraicCurve.Divisor" in

theorem Divisor.degree_nonneg_of_nonneg [IsCurveOver K F]
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [Divisor.degree_eq_sum_support_port]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (hD v) (Int.natCast_nonneg _)
theorem lSpace_eq_bot_of_degree_neg [IsCurveOver K F]
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨P, hPord, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have heff : ∀ v : Place K F, 0 ≤ (P + D) v := by
    intro v
    rw [Finsupp.add_apply, hPord]
    rcases mem_lSpace_iff_ord.mp hf with rfl | h
    · exact absurd rfl hf0
    · linarith [h v]
  have hdegPD : 0 ≤ Divisor.degree (P + D) := Divisor.degree_nonneg_of_nonneg heff
  rw [map_add, hPdeg, zero_add] at hdegPD
  exact absurd hdegPD (not_le.mpr hD)
theorem ell_eq_zero_of_degree_neg [IsCurveOver K F] (hD : Divisor.degree D < 0) :
    ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]
end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum_support.AlgebraicCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_Divisor_degree_eq_sum_support.AlgebraicCurve" in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  AlgebraicCurve.Divisor.degree_eq_sum_support_port (K := K) (F := F) (D := D)
end S_AlgebraicCurve_Divisor_degree_eq_sum_support
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
