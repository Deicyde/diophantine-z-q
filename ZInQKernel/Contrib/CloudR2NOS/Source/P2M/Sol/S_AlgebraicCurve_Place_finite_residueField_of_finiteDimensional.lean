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
  Source file    : P2M/Sol/S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean
  Source sha256  : afdd5394bae9a0193839cb0861449d26fbdd90ce3f7f7002b040aa338f3e9668
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
r2nos_namespace_dual

open AlgebraicCurve
r2nos_open_dual "AlgebraicCurve"

namespace S09G2F
r2nos_namespace_dual
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']

open IsLocalRing in
r2nos_open_dual "IsLocalRing" in

theorem linearIndependent_lift (w : Place K F') {ι : Type*} [Fintype ι]
    (x : ι → w.toValuationSubring)
    (hx : LinearIndependent (w.restrict F).ResidueField
      fun i => (residue w.toValuationSubring (x i) : w.ResidueField)) :
    LinearIndependent F fun i => ((x i : w.toValuationSubring) : F') := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := not_forall.mp hne
  set O : ValuationSubring F := (w.restrict F).toValuationSubring

  have hne' : (Finset.univ.filter fun i => g i ≠ 0).Nonempty := ⟨i₀, by simpa using hi₀⟩
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image _ (fun i => O.valuation (g i)) hne'
  have hgk : g k ≠ 0 := by simpa using hk

  have hb : ∀ i, g i / g k ∈ O := by
    intro i
    by_cases hi : g i = 0
    · simp [hi]
    · apply O.mem_of_valuation_le_one
      rw [map_div₀]
      have hk0 : (0 : O.ValueGroup) < O.valuation (g k) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hgk
      exact (div_le_one₀ hk0).mpr (hkmax i (by simpa using hi))
  let b : ι → O := fun i => ⟨g i / g k, hb i⟩

  have hrel : ∑ i, Place.restrictInclusion F w (b i) * x i = 0 := by
    apply Subtype.ext
    have hcoe : ((∑ i, Place.restrictInclusion F w (b i) * x i : w.toValuationSubring) : F') =
        ∑ i, algebraMap F F' (g i / g k) * (x i : F') := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, Place.coe_restrictInclusion]
    rw [hcoe]
    have : ∑ i, algebraMap F F' (g i / g k) * (x i : F') =
        algebraMap F F' (g k)⁻¹ * ∑ i, g i • ((x i : w.toValuationSubring) : F') := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, div_eq_inv_mul, map_mul, mul_assoc]
    rw [this, hg, mul_zero]
    rfl

  have hres : ∑ i, (residue O (b i) : (w.restrict F).ResidueField) •
      (residue w.toValuationSubring (x i) : w.ResidueField) = 0 := by
    have h := congrArg (residue w.toValuationSubring) hrel
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue,
      map_mul]
  have hk1 := (Fintype.linearIndependent_iff.mp hx) _ hres k

  have hbk : b k = 1 := Subtype.ext (div_self hgk)
  rw [hbk, map_one] at hk1
  exact one_ne_zero hk1

open IsLocalRing in
r2nos_open_dual "IsLocalRing" in

theorem finite_residueField (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by
  classical
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := Module.finrank F F') fun s hs => ?_)
    Cardinal.natCast_lt_aleph0

  choose x hx using fun y : s => residue_surjective (R := w.toValuationSubring) (y : w.ResidueField)
  have hs' : LinearIndependent (w.restrict F).ResidueField
      fun i : s => (residue w.toValuationSubring (x i) : w.ResidueField) := by
    simpa only [hx] using hs
  have := linearIndependent_lift (F := F) w x hs'
  simpa [Fintype.card_coe] using this.fintype_card_le_finrank

end S09G2F

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] (w : Place K F') : Module.Finite (w.restrict F).ResidueField w.ResidueField :=
  S09G2F.finite_residueField (F := F) w
end S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
