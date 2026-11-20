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
  Source file    : P2M/Sol/S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range.lean
  Source sha256  : 5232d3000e7f6da6e89ec4661ac6a8f3f2dd056d3dfd0406a10f3e91a4b2c7cb
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
r2nos_namespace_dual

set_option autoImplicit false

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

namespace P2mGeomIrred
r2nos_namespace_dual

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]

set_option backward.isDefEq.respectTransparency false in

theorem main [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime := by
  classical
  obtain ⟨q, hq⟩ := ExpChar.exists K
  set Ωs : IntermediateField K Ω := separableClosure K Ω with hΩs

  have hF : IsField (L ⊗[K] Ωs) :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range K L Ωs hsc
  letI : Field (L ⊗[K] Ωs) := hF.toField

  let ι : L ⊗[K] Ωs →ₐ[K] L ⊗[K] Ω := Algebra.TensorProduct.map (AlgHom.id K L) Ωs.val
  have hι : Function.Injective ι := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L)
      (Ωs.val.toLinearMap) Subtype.val_injective
    intro a b hab
    apply h
    change ι a = ι b
    exact hab

  haveI : Nontrivial (L ⊗[K] Ω) :=
    (Algebra.TensorProduct.includeLeft_injective (R := K) (A := L) (B := Ω) (S := K)
      (algebraMap K Ω).injective).nontrivial
  haveI : ExpChar (L ⊗[K] Ω) q :=
    expChar_of_injective_algebraMap (algebraMap K (L ⊗[K] Ω)).injective q

  have hmono : ∀ (t : L ⊗[K] Ω) (n m : ℕ), t ^ q ^ n ∈ ι.range → t ^ q ^ (n + m) ∈ ι.range := by
    intro t n m ht
    have : t ^ q ^ (n + m) = (t ^ q ^ n) ^ q ^ m := by rw [← pow_mul, ← pow_add]
    rw [this]
    exact pow_mem ht _
  have hpow : ∀ t : L ⊗[K] Ω, ∃ n : ℕ, t ^ q ^ n ∈ ι.range := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l ω =>
      obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem Ωs q).mp inferInstance ω
      refine ⟨n, (l ^ q ^ n) ⊗ₜ[K] y, ?_⟩
      change ι ((l ^ q ^ n) ⊗ₜ[K] y) = _
      rw [Algebra.TensorProduct.tmul_pow]
      simp only [ι, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
      congr 1
    | add a b ha hb =>
      obtain ⟨n, ha⟩ := ha
      obtain ⟨m, hb⟩ := hb
      refine ⟨n + m, ?_⟩
      rw [add_pow_expChar_pow]
      refine add_mem (hmono a n m ha) ?_
      rw [add_comm n m]
      exact hmono b m n hb

  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : L ⊗[K] Ω) ∈ nilradical (L ⊗[K] Ω) := htop ▸ Submodule.mem_top
    rw [mem_nilradical] at h1
    obtain ⟨N, hN⟩ := h1
    rw [one_pow] at hN
    exact one_ne_zero hN
  · intro a b hab
    rw [mem_nilradical] at hab
    obtain ⟨N, hN⟩ := hab
    obtain ⟨n, α, hα⟩ := hpow a
    obtain ⟨m, β, hβ⟩ := hpow b
    replace hα : ι α = a ^ q ^ n := hα
    replace hβ : ι β = b ^ q ^ m := hβ
    have hα' : ι (α ^ q ^ m) = a ^ q ^ (n + m) := by
      rw [map_pow, hα, ← pow_mul, ← pow_add]
    have hβ' : ι (β ^ q ^ n) = b ^ q ^ (n + m) := by
      rw [map_pow, hβ, ← pow_mul, ← pow_add, add_comm]
    have h0 : (α ^ q ^ m * β ^ q ^ n) ^ N = 0 := by
      apply hι
      rw [map_pow, map_mul, hα', hβ', ← mul_pow, ← pow_mul, mul_comm (q ^ (n + m)) N, pow_mul,
        hN, zero_pow (pow_ne_zero _ (expChar_pos K q).ne'), map_zero]
    have h1 : α ^ q ^ m * β ^ q ^ n = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rcases mul_eq_zero.mp h1 with h | h
    · left
      rw [mem_nilradical]
      refine ⟨q ^ (n + m), ?_⟩
      rw [← hα', h, map_zero]
    · right
      rw [mem_nilradical]
      refine ⟨q ^ (n + m), ?_⟩
      rw [← hβ', h, map_zero]

end P2mGeomIrred

universe u v w

theorem solution
    (K : Type u) (L : Type v) (Ω : Type w) [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime :=
  P2mGeomIrred.main hsc
end S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
