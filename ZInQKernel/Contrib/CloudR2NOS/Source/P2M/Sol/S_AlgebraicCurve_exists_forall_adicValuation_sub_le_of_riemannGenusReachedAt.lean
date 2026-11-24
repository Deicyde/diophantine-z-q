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
  Source file    : P2M/Sol/S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt.lean
  Source sha256  : da41088bfc7d36af07dd501646f20a28168b47e646ca772b61fd300120c5d4a1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 10 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_adeleSpace_eq_of_genusReached
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_one_le_deg
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_ell_add_of_forall_eq_ord
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
r2nos_namespace_dual

set_option autoImplicit false

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver LSpace ell mem_lSpace_iff_ord mem_adeleBdd diagonalHom_apply adeleSpace adeleBdd_le_adeleSpace RiemannGenusReachedAt finiteDimensional_lSpace RiemannGenusReachedAt.eq_of_ge adeleSpace_eq_of_genusReached one_le_deg ell_add_of_forall_eq_ord"
w03_open "AlgebraicCurve"

theorem strongApprox_aux {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F)
    (α : Place K F → F) (hα : {v | ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite) :
    ∃ f : F, ∀ v ∈ S, v.adicValuation (α v - f) ≤ WithZero.exp (D v) := by
  classical
  haveI : Nonempty (Place K F) := ⟨v₀⟩

  have hαA : α ∈ adeleSpace K F := by
    set T : Finset (Place K F) := hα.toFinset with hT
    have hmemT : ∀ v, v ∈ T ↔ ¬ v.adicValuation (α v) ≤ WithZero.exp (D v) := fun v => by
      rw [hT, Set.Finite.mem_toFinset]; rfl
    set c : ℕ := T.sup fun v => (-(v.ord (α v)) - D v).toNat with hc
    have hcv : ∀ v ∈ T, -(v.ord (α v)) - D v ≤ (c : ℤ) := by
      intro v hv
      have h1 : (-(v.ord (α v)) - D v).toNat ≤ c :=
        Finset.le_sup (f := fun v => (-(v.ord (α v)) - D v).toNat) hv
      have h2 : ((-(v.ord (α v)) - D v).toNat : ℤ) ≤ (c : ℤ) := by exact_mod_cast h1
      omega
    let E : Divisor K F := D + T.sum fun w => (c : ℤ) • Finsupp.single w 1
    have hE : ∀ v, E v = D v + if v ∈ T then (c : ℤ) else 0 := by
      intro v
      first
        | simp only [E, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
            Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.sum_ite_eq]
        | simp only [E, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
            Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.sum_ite_eq]
    refine adeleBdd_le_adeleSpace (D := E) (fun v => ?_)
    by_cases hv : v ∈ T
    · have hbad := (hmemT v).mp hv
      have hα0 : α v ≠ 0 := fun h0 => hbad (by rw [h0]; simp)
      rw [v.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hE, if_pos hv]
      have := hcv v hv
      omega
    · have hok : v.adicValuation (α v) ≤ WithZero.exp (D v) := by
        by_contra h'
        exact hv ((hmemT v).mpr h')
      refine hok.trans ?_
      rw [WithZero.exp_le_exp, hE, if_neg hv, add_zero]

  have hdeg₀ : (1 : ℤ) ≤ v₀.deg := by exact_mod_cast one_le_deg (K := K) v₀
  set N : Divisor K F := D ⊓ 0 with hN
  set m : ℕ := (γ + Divisor.degree D₀ - Divisor.degree N).toNat with hm
  have hm' : γ + Divisor.degree D₀ - Divisor.degree N ≤ (m : ℤ) := by
    rw [hm]; exact Int.self_le_toNat _
  set W : Divisor K F := (m : ℤ) • Finsupp.single v₀ 1 + N with hW
  have hWdeg : Divisor.degree W = (m : ℤ) * v₀.deg + Divisor.degree N := by
    rw [hW, map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
  have hWv : ∀ v ∈ S, W v ≤ D v := by
    intro v hv
    have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
    have hs : (Finsupp.single v₀ (1 : ℤ)) v = 0 := by simp [Finsupp.single_apply, hne, hne.symm]
    rw [hW, Finsupp.add_apply, Finsupp.smul_apply, hs, smul_zero, zero_add, hN, Finsupp.inf_apply]
    exact inf_le_left

  set A : Divisor K F := W - D₀ with hA
  have hAdeg : γ ≤ Divisor.degree A := by
    rw [hA, map_sub, hWdeg]
    have : (m : ℤ) ≤ (m : ℤ) * v₀.deg := by nlinarith
    omega
  have hellA : 0 < ell A := by
    have := h.isMax A
    omega
  haveI : Nontrivial ↥(LSpace A) := Module.nontrivial_of_finrank_pos hellA
  obtain ⟨⟨z, hzA⟩, hz0'⟩ := exists_ne (0 : ↥(LSpace A))
  have hz0 : z ≠ 0 := fun h0 => hz0' (Subtype.ext h0)
  obtain ⟨P, hP, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
  have hzord : ∀ v, -A v ≤ v.ord z := ((mem_lSpace_iff_ord).mp hzA).resolve_left hz0
  have hD₀le : D₀ ≤ W + P := by
    intro v
    have h1 := hzord v
    rw [hA, Finsupp.sub_apply] at h1
    rw [Finsupp.add_apply, hP v]
    omega

  have hreach' := h.eq_of_ge hD₀le
  have hellWP : ell (W + P) = ell W := ell_add_of_forall_eq_ord W hz0 hP
  have hdegWP : Divisor.degree (W + P) = Divisor.degree W := by rw [map_add, hPdeg, add_zero]
  have hreachW : RiemannGenusReachedAt γ W :=
    ⟨finiteDimensional_lSpace (K := K) (F := F) W, by rw [← hdegWP, ← hellWP]; exact hreach',
      h.isMax⟩

  have hSA := adeleSpace_eq_of_genusReached hreachW
  rw [hSA, Submodule.mem_sup] at hαA
  obtain ⟨a, ha, g, hg, hag⟩ := hαA
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hg
  refine ⟨f, fun v hv => ?_⟩
  have hav : α v - f = a v := by
    have := congrFun hag v
    rw [Pi.add_apply, diagonalHom_apply] at this
    rw [← this]; ring
  rw [hav]
  exact ((mem_adeleBdd.mp ha) v).trans (WithZero.exp_le_exp.mpr (hWv v hv))

end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt.AlgebraicCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt.AlgebraicCurve" in

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F)
    (α : Place K F → F) (hα : {v | v ∈ S ∧ ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite) :
    ∃ f : F, ∀ v ∈ S, v.adicValuation (α v - f) ≤ WithZero.exp (D v) := by
  classical

  set α' : Place K F → F := fun v => if v ∈ S then α v else 0 with hα'
  have hα'fin : {v : Place K F | ¬ v.adicValuation (α' v) ≤ WithZero.exp (D v)}.Finite := by
    refine hα.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    by_cases hvS : v ∈ S
    · simp only [hα', if_pos hvS] at hv
      exact ⟨hvS, hv⟩
    · simp only [hα', if_neg hvS] at hv
      exact absurd (by simp) hv
  obtain ⟨f, hf⟩ := strongApprox_aux h S hv₀ D α' hα'fin
  refine ⟨f, fun v hv => ?_⟩
  have := hf v hv
  simp only [hα', if_pos hv] at this
  exact this
end S_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
