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
  Source file    : Definitions/Def_AdicCompletionLocalRing.lean
  Source sha256  : 9a7faeda47ecd6fee70a5881e0ce2d8f746ecfe6dd812b33c3cfc63bbef850b9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-2 HAND REPAIRS (lane4, recorded): `algebraMap_apply` is now ambiguous with `_root_.algebraMap_apply` (ContinuousMap); the so… (×1)
-/

import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open IsLocalRing
r2nos_open_dual "IsLocalRing"

namespace AdicCompletion
r2nos_namespace_dual

variable {A : Type*} [CommRing A]

section Kernel

variable (I : Ideal A)

theorem evalₐ_algebraMap (n : ℕ) (a : A) :
    evalₐ I n (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk _ a := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, evalₐ_of]

theorem mem_ker_evalₐ_iff (n : ℕ) (x : AdicCompletion I A) :
    x ∈ RingHom.ker (evalₐ I n) ↔ x ∈ LinearMap.ker (eval I A n) := by
  have h : (I ^ n • ⊤ : Ideal A) = I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [RingHom.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx; rw [← factor_evalₐ_eq_eval I x h.ge, hx]; exact RingHom.map_zero _
  · intro hx; rw [← factor_eval_eq_evalₐ I x h.le, hx]; exact LinearMap.map_zero _

theorem ker_evalₐ_eq_map_pow (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n) = (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  rw [mem_ker_evalₐ_iff, ← pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Submodule.restrictScalars_mem]

theorem exists_eq_algebraMap_add (hI : I.FG) (n : ℕ) (x : AdicCompletion I A) :
    ∃ a : A, ∃ y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)),
      x = algebraMap A (AdicCompletion I A) a + y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨a, x - algebraMap A _ a, ?_, by ring⟩
  rw [← ker_evalₐ_eq_map_pow I hI, RingHom.mem_ker, map_sub, evalₐ_algebraMap, ha, sub_self]

theorem isUnit_one_add_of_mem_map (hI : I.FG) {x : AdicCompletion I A}
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (1 + x) := by
  haveI : IsAdicComplete (I.map (algebraMap A (AdicCompletion I A))) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I A)).mpr (isAdicComplete hI)
  have h := Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot _ hx) 1
  rwa [mul_one, add_comm] at h

theorem isUnit_add_of_mem_map (hI : I.FG) {u x : AdicCompletion I A} (hu : IsUnit u)
    (hx : x ∈ I.map (algebraMap A (AdicCompletion I A))) : IsUnit (u + x) := by
  have e : u + x = u * (1 + ↑hu.unit⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [e]
  exact hu.mul (isUnit_one_add_of_mem_map I hI (Ideal.mul_mem_left _ _ hx))

end Kernel

section Local

variable [IsLocalRing A]

theorem isUnit_of_isUnit_algebraMap {a : A}
    (h : IsUnit (algebraMap A (AdicCompletion (maximalIdeal A) A) a)) : IsUnit a := by
  by_contra ha
  have hmem : a ∈ maximalIdeal A ^ 1 := by
    rw [pow_one]; exact (mem_maximalIdeal a).mpr ha
  have h1 := h.map (evalₐ (maximalIdeal A) 1)
  rw [evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, isUnit_zero_iff] at h1
  exact (maximalIdeal.isMaximal A).ne_top
    ((pow_one (maximalIdeal A)).symm.trans (Ideal.Quotient.zero_eq_one_iff.mp h1))

theorem isUnit_one_add_of_mem_map_maximalIdeal (h𝔪 : (maximalIdeal A).FG)
    {x : AdicCompletion (maximalIdeal A) A}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    IsUnit (1 + x) :=
  isUnit_one_add_of_mem_map _ h𝔪 hx

variable [IsNoetherianRing A]

theorem maximalIdeal_fg : (maximalIdeal A).FG := IsNoetherian.noetherian _

instance instIsLocalRingMaximalIdeal : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
  isLocalRing_of_fg maximalIdeal_fg

theorem maximalIdeal_pow_eq_ker_evalₐ (n : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n = RingHom.ker (evalₐ (maximalIdeal A) n) := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow, ker_evalₐ_eq_map_pow _ maximalIdeal_fg]

theorem maximalIdeal_eq_ker_evalₐ_one :
    maximalIdeal (AdicCompletion (maximalIdeal A) A) = RingHom.ker (evalₐ (maximalIdeal A) 1) := by
  rw [← maximalIdeal_pow_eq_ker_evalₐ, pow_one]

theorem mem_maximalIdeal_iff (x : AdicCompletion (maximalIdeal A) A) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ↔ evalₐ (maximalIdeal A) 1 x = 0 := by
  rw [maximalIdeal_eq_ker_evalₐ_one, RingHom.mem_ker]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k A]

noncomputable def quotientMaximalIdealPowAlgHom (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      →ₐ[k] A ⧸ maximalIdeal A ^ n :=
  Ideal.Quotient.liftₐ _ ((evalₐ (maximalIdeal A) n).restrictScalars k) fun x hx => by
    rwa [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker] at hx

theorem quotientMaximalIdealPowAlgHom_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgHom k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

theorem quotientMaximalIdealPowAlgHom_bijective (n : ℕ) :
    Function.Bijective (quotientMaximalIdealPowAlgHom (A := A) k n) := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [quotientMaximalIdealPowAlgHom_mk, quotientMaximalIdealPowAlgHom_mk] at hxy
    refine Ideal.Quotient.eq.mpr ?_
    rw [maximalIdeal_pow_eq_ker_evalₐ, RingHom.mem_ker, map_sub, hxy, sub_self]
  · intro z
    obtain ⟨x, rfl⟩ := surjective_evalₐ (maximalIdeal A) n z
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩

noncomputable def quotientMaximalIdealPowAlgEquiv (n : ℕ) :
    (AdicCompletion (maximalIdeal A) A ⧸ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  AlgEquiv.ofBijective _ (quotientMaximalIdealPowAlgHom_bijective k n)

theorem quotientMaximalIdealPowAlgEquiv_mk (n : ℕ) (x : AdicCompletion (maximalIdeal A) A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ x) = evalₐ (maximalIdeal A) n x :=
  rfl

theorem quotientMaximalIdealPowAlgEquiv_mk_algebraMap (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquiv k n (Ideal.Quotient.mk _ (algebraMap A _ a))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquiv_mk, evalₐ_algebraMap]

end Scalars

end Local

section Transport

variable [IsLocalRing A] [IsNoetherianRing A]
variable {k : Type*} [CommRing k] [Algebra k A] {B : Type*} [CommRing B] [IsLocalRing B] [Algebra k B]
variable (Φ : AdicCompletion (maximalIdeal A) A ≃ₐ[k] B)

omit [IsNoetherianRing A] [IsLocalRing B] in
theorem isUnit_algEquiv_iff (x : AdicCompletion (maximalIdeal A) A) : IsUnit (Φ x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map Φ.symm, fun h => h.map Φ⟩

theorem comap_maximalIdeal_algEquiv :
    (maximalIdeal B).comap (Φ : AdicCompletion (maximalIdeal A) A →+* B)
      = maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  ext x
  show Φ x ∈ maximalIdeal B ↔ x ∈ maximalIdeal _
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_algEquiv_iff]

theorem map_maximalIdeal_algEquiv :
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)).map
        (Φ : AdicCompletion (maximalIdeal A) A →+* B) = maximalIdeal B := by
  rw [← comap_maximalIdeal_algEquiv Φ]
  exact Ideal.map_comap_of_surjective _ Φ.surjective _

theorem maximalIdeal_eq_map_algEquiv :
    maximalIdeal B = (maximalIdeal A).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [← Ideal.map_map, ← maximalIdeal_eq_map, map_maximalIdeal_algEquiv]

theorem maximalIdeal_pow_eq_map_algEquiv (n : ℕ) :
    maximalIdeal B ^ n = (maximalIdeal A ^ n).map
      ((Φ : AdicCompletion (maximalIdeal A) A →+* B).comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [Ideal.map_pow, ← maximalIdeal_eq_map_algEquiv]

theorem algEquiv_algebraMap_mem_maximalIdeal {a : A} (ha : a ∈ maximalIdeal A) :
    Φ (algebraMap A _ a) ∈ maximalIdeal B := by
  rw [maximalIdeal_eq_map_algEquiv Φ]
  exact Ideal.mem_map_of_mem _ ha

noncomputable def quotientMaximalIdealPowAlgEquivOfAlgEquiv (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) ≃ₐ[k] A ⧸ maximalIdeal A ^ n :=
  (Ideal.quotientEquivAlg (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) (maximalIdeal B ^ n)
    Φ (by rw [Ideal.map_pow, map_maximalIdeal_algEquiv])).symm.trans
    (quotientMaximalIdealPowAlgEquiv k n)

theorem quotientMaximalIdealPowAlgEquivOfAlgEquiv_mk (n : ℕ) (a : A) :
    quotientMaximalIdealPowAlgEquivOfAlgEquiv Φ n (Ideal.Quotient.mk _ (Φ (algebraMap A _ a)))
      = Ideal.Quotient.mk _ a := by
  rw [quotientMaximalIdealPowAlgEquivOfAlgEquiv, AlgEquiv.trans_apply,
    ← Ideal.quotientEquivAlg_mk (I := maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n)
      (J := maximalIdeal B ^ n) (f := Φ) (hIJ := by rw [Ideal.map_pow, map_maximalIdeal_algEquiv]),
    AlgEquiv.symm_apply_apply, quotientMaximalIdealPowAlgEquiv_mk_algebraMap]

end Transport

end AdicCompletion

#print axioms AdicCompletion.ker_evalₐ_eq_map_pow
#print axioms AdicCompletion.isUnit_one_add_of_mem_map
#print axioms AdicCompletion.instIsLocalRingMaximalIdeal
#print axioms AdicCompletion.maximalIdeal_eq_map
#print axioms AdicCompletion.quotientMaximalIdealPowAlgEquiv
#print axioms AdicCompletion.maximalIdeal_eq_map_algEquiv
#print axioms AdicCompletion.quotientMaximalIdealPowAlgEquivOfAlgEquiv

end ZInQ.Contrib.CloudW03NeronSurj.FLT
