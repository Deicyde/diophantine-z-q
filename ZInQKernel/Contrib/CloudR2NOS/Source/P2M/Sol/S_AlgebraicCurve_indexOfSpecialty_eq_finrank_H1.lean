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
  Source file    : P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean
  Source sha256  : c0f6472cc049d60f124a21f26ba635fe6f98eae05284e1c0cdb4319547d32199
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
r2nos_namespace_dual

set_option autoImplicit false

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor repartitions mem_repartitions_of_forall_le_exp repartitionsOf principalRepartitions mem_principalRepartitions_iff H1 adeleBdd diagonalHom adeleSpace adeleBdd_le_adeleSpace globalSub indexOfSpecialty mem_adeleSpace_iff adeleBddPrincipal indexOfSpecialty_eq"
w03_open "AlgebraicCurve"

open WithZero
r2nos_open_dual "WithZero"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_repartitionsOf_iff_coe_mem_adeleBdd {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl

theorem mem_repartitions_of_mem_adeleBdd {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    α ∈ repartitions K F :=
  mem_repartitions_of_forall_le_exp D α hα

theorem mem_repartitions_of_mem_adeleSpace {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    α ∈ repartitions K F := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact mem_repartitions_of_mem_adeleBdd hD

theorem diagonalHom_eq_coe_algebraMap (f : F) :
    diagonalHom K F f = ((algebraMap F ↥(repartitions K F) f : ↥(repartitions K F)) : Place K F → F) := rfl

theorem mem_principalRepartitions_iff_coe_mem_globalSub {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔ (α : Place K F → F) ∈ globalSub K F := by
  rw [mem_principalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

noncomputable def boundedFamilies [HasPrincipalDivisors K F] : Subalgebra F (Place K F → F) where
  carrier := {α | ∃ D : Divisor K F, ∀ v : Place K F, v.adicValuation (α v) ≤ exp (D v)}
  mul_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D + E, fun v => ?_⟩
    rw [Pi.mul_apply, map_mul, Finsupp.add_apply, exp_add]
    exact mul_le_mul' (hD v) (hE v)
  add_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D ⊔ E, fun v => ?_⟩
    rw [Pi.add_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · exact (hD v).trans (exp_le_exp.mpr (le_sup_left (a := D) (b := E) v))
    · exact (hE v).trans (exp_le_exp.mpr (le_sup_right (a := D) (b := E) v))
  algebraMap_mem' := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · exact ⟨0, fun v => by simp⟩
    · obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
      refine ⟨-P, fun v => ?_⟩
      rw [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        v.adicValuation_eq_exp_neg_ord hf, Finsupp.neg_apply, hP]

theorem mem_adeleSpace_iff_mem_repartitions [HasPrincipalDivisors K F] {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F := by
  constructor
  · exact mem_repartitions_of_mem_adeleSpace
  · intro hα
    have h : repartitions K F ≤ boundedFamilies (K := K) (F := F) := by
      refine Algebra.adjoin_le ?_
      intro β hβ
      classical
      let S : Finset (Place K F) := hβ.toFinset
      refine ⟨∑ v ∈ S, Finsupp.single v (-(v.ord (β v))), fun v => ?_⟩
      by_cases hv : v ∈ S
      · have hβv : β v ≠ 0 := by
          intro h0
          have : ¬v.adicValuation (β v) ≤ 1 := by simpa [S] using hv
          apply this; simp [h0]
        rw [v.adicValuation_eq_exp_neg_ord hβv, exp_le_exp, Finsupp.finset_sum_apply,
          Finset.sum_eq_single v (fun w _ hw => Finsupp.single_eq_of_ne (Ne.symm hw)) (fun h => (h hv).elim),
          Finsupp.single_eq_same]
      · have : v.adicValuation (β v) ≤ 1 := by
          by_contra h; exact hv (by simpa [S] using h)
        refine this.trans ?_
        rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero (fun w hw => ?_), exp_zero]
        exact Finsupp.single_eq_of_ne (fun h => hv (h ▸ hw))
    obtain ⟨D, hD⟩ := h hα
    exact adeleBdd_le_adeleSpace (D := D) hD

theorem adeleSpace_eq_restrictScalars_repartitions [HasPrincipalDivisors K F] :
    adeleSpace K F = (Subalgebra.toSubmodule (repartitions K F)).restrictScalars K := by
  ext α
  exact mem_adeleSpace_iff_mem_repartitions

noncomputable def adeleSpaceEquivRepartitions [HasPrincipalDivisors K F] :
    ↥(adeleSpace K F) ≃ₗ[K] ↥(repartitions K F) where
  toFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mp α.2⟩
  invFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mpr α.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.AlgebraicCurve WithZero in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.AlgebraicCurve WithZero" in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (D : Divisor K F) :
    indexOfSpecialty D = Module.finrank K (H1 D) := by
  let e := adeleSpaceEquivRepartitions (K := K) (F := F)
  have hmap : (adeleBddPrincipal K F D).map (e : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F))
      = repartitionsOf D ⊔ principalRepartitions K F := by
    rw [Submodule.map_sup]
    congr 1
    · ext α
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact hβ
      · intro hα; exact ⟨e.symm α, hα, e.apply_symm_apply α⟩
    · ext α
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact mem_principalRepartitions_iff_coe_mem_globalSub.mpr hβ
      · intro hα
        exact ⟨e.symm α, mem_principalRepartitions_iff_coe_mem_globalSub.mp hα, e.apply_symm_apply α⟩
  rw [indexOfSpecialty_eq]
  exact LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ e hmap)
end S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
