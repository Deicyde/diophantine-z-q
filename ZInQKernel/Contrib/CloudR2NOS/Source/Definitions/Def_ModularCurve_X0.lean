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
  Source file    : Definitions/Def_ModularCurve_X0.lean
  Source sha256  : 7563047a0e7ddf99fcf3e52e65bb60634e25daf2d7ddb41cf3e5e3aa06160a23
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology
r2nos_open_scoped_dual "PowerSeries.WithPiTopology"

open PowerSeries HahnSeries IntermediateField
r2nos_open_dual "PowerSeries HahnSeries IntermediateField"

namespace ModularCurve
r2nos_namespace_dual

section QExpand

variable {R : Type*} [CommRing R]

variable (R) in

def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

variable (N : ℕ) [NeZero N]

@[simp]
theorem qExpand_coeff_mul (f : LaurentSeries R) (k : ℤ) :
    (qExpand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

theorem qExpand_coeff_of_not_dvd (f : LaurentSeries R) {k : ℤ} (hk : ¬ (N : ℤ) ∣ k) :
    (qExpand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩

@[simp]
theorem qExpand_single (k : ℤ) (r : R) :
    qExpand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single

@[simp]
theorem qExpand_C (r : R) : qExpand R N (HahnSeries.C r) = HahnSeries.C r :=
  HahnSeries.embDomainRingHom_C

theorem qExpand_injective : Function.Injective (qExpand R N) :=
  HahnSeries.embDomain_injective

theorem qExpand_one_apply (f : LaurentSeries R) : qExpand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [qExpand_coeff_mul]

theorem qExpand_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) (f : LaurentSeries R) :
    qExpand R M f = qExpand R K f := by
  subst h; rfl

theorem qExpand_qExpand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    qExpand R M (qExpand R N f) = qExpand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, qExpand_coeff_mul,
        qExpand_coeff_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [qExpand_coeff_mul M _ m]
      refine qExpand_coeff_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact qExpand_coeff_of_not_dvd M _ hkM

end QExpand

section RatAlgebra

variable (N : ℕ) [NeZero N]

theorem algebraMap_apply_eq_single (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c := by
  have h1 : algebraMap ℚ (PowerSeries ℚ) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

def qExpandₐ : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries ℚ where
  __ := qExpand ℚ N
  commutes' r := by
    show qExpand ℚ N (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r
    rw [algebraMap_apply_eq_single, qExpand_single, mul_zero]

@[simp]
theorem qExpandₐ_apply (f : LaurentSeries ℚ) : qExpandₐ N f = qExpand ℚ N f := rfl

end RatAlgebra

section JFunction

def eisenstein4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

@[simp]
theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein4]

def etaProd : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

theorem constantCoeff_etaProd : PowerSeries.constantCoeff etaProd = 1 := by
  rw [etaProd]
  simp [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ)]

def dedekindEtaUnit : PowerSeries ℤ := etaProd ^ 24

theorem constantCoeff_dedekindEtaUnit : PowerSeries.constantCoeff dedekindEtaUnit = 1 := by
  rw [dedekindEtaUnit, map_pow, constantCoeff_etaProd, one_pow]

def dedekindEtaUnitInv : PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1

theorem dedekindEtaUnit_mul_inv : dedekindEtaUnit * dedekindEtaUnitInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_dedekindEtaUnit]; rfl)

theorem constantCoeff_dedekindEtaUnitInv :
    PowerSeries.constantCoeff dedekindEtaUnitInv = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) dedekindEtaUnit_mul_inv
  rwa [map_mul, constantCoeff_dedekindEtaUnit, one_mul, map_one] at h

def jNum : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv

@[simp]
theorem constantCoeff_jNum : PowerSeries.constantCoeff jNum = 1 := by
  rw [jNum, map_mul, map_pow, constantCoeff_eisenstein4, constantCoeff_dedekindEtaUnitInv,
    one_pow, one_mul]

def jNumQ : PowerSeries ℚ := jNum.map (Int.castRingHom ℚ)

@[simp]
theorem constantCoeff_jNumQ : PowerSeries.constantCoeff jNumQ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, jNumQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
  simp

def jq : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ

theorem ofPowerSeries_coeff_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))

theorem jq_pow (n : ℕ) :
    jq ^ n = HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (jNumQ ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jq, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem coeff_jq_pow_self (n : ℕ) : (jq ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNumQ, one_pow]

theorem coeff_jq_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jq ^ n).coeff m = 0 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

@[simp]
theorem coeff_jq_neg_one : jq.coeff (-1 : ℤ) = 1 := by
  have h := coeff_jq_pow_self 1
  simpa using h

theorem coeff_jq_of_lt {k : ℤ} (hk : k < -1) : jq.coeff k = 0 := by
  have h := coeff_jq_pow_of_lt (n := 1) (m := k) (by simpa using hk)
  simpa using h

theorem jq_ne_zero : jq ≠ 0 := fun h => by simpa [h] using coeff_jq_neg_one

end JFunction

def jqN (N : ℕ) [NeZero N] : LaurentSeries ℚ := qExpand ℚ N jq

@[simp]
theorem jqN_one : jqN 1 = jq := qExpand_one_apply jq

section NamedInputs

def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, if_pos squarefree_one]
  simp

def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

@[simp]
theorem evalAtJ_X : evalAtJ Polynomial.X = jq := by
  simp [evalAtJ]

structure ModularPolynomialData (N : ℕ) [NeZero N] : Type where

  Φ : Polynomial (Polynomial ℤ)

  monic : Φ.Monic

  natDegree_eq : Φ.natDegree = dedekindPsi N

  eval_eq_zero : Φ.eval₂ evalAtJ (jqN N) = 0

def modularPolynomialDataOne : ModularPolynomialData 1 where
  Φ := Polynomial.X - Polynomial.C Polynomial.X
  monic := Polynomial.monic_X_sub_C _
  natDegree_eq := by simp
  eval_eq_zero := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, jqN_one,
      evalAtJ_X, sub_self]

def FunctionFieldGeneration (M : ℕ) [NeZero M] : Prop :=
  ∀ d : ℕ, d ∣ M → ∀ (_ : NeZero d), qExpand ℚ d jq ∈
    IntermediateField.adjoin ℚ {jq, qExpand ℚ M jq}

theorem functionFieldGeneration_one : FunctionFieldGeneration 1 := by
  intro d hd hne
  haveI := hne
  rw [Nat.dvd_one] at hd
  subst hd
  exact subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

end NamedInputs

section FunctionField

variable (N : ℕ) [NeZero N]

def modularFunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq}

theorem jq_mem : jq ∈ modularFunctionField N :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

theorem jqN_mem : qExpand ℚ N jq ∈ modularFunctionField N :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

theorem modularFunctionField_one : modularFunctionField 1 = ℚ⟮jq⟯ := by
  rw [modularFunctionField, qExpand_one_apply, Set.pair_eq_singleton]

theorem adjoin_jq_le : ℚ⟮jq⟯ ≤ modularFunctionField N := by
  rw [IntermediateField.adjoin_le_iff]
  exact Set.singleton_subset_iff.mpr (jq_mem N)

end FunctionField

def jGen : ℚ⟮jq⟯ := ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩

def evalAtJGen : Polynomial ℤ →+* ℚ⟮jq⟯ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℚ⟮jq⟯) jGen

theorem algebraMap_comp_evalAtJGen :
    (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)).comp evalAtJGen = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ) (evalAtJGen Polynomial.X) = evalAtJ Polynomial.X
  rw [evalAtJ_X]
  show algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)
    (Polynomial.eval₂ (Int.castRingHom ℚ⟮jq⟯) jGen Polynomial.X) = jq
  rw [Polynomial.eval₂_X]
  rfl

namespace ModularPolynomialData
r2nos_namespace_dual

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

def toAdjoin : Polynomial ℚ⟮jq⟯ := data.Φ.map evalAtJGen

theorem toAdjoin_monic : data.toAdjoin.Monic := data.monic.map _

end ModularPolynomialData

section AllDivisors

variable (N : ℕ) [NeZero N]

def divisorExpansions : Set (LaurentSeries ℚ) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand ℚ d jq}

omit [NeZero N] in
theorem mem_divisorExpansions {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand ℚ d jq ∈ divisorExpansions N :=
  ⟨d, ‹_›, hd, rfl⟩

def modularFunctionFieldFull : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions N)

omit [NeZero N] in
theorem jqd_mem_full {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand ℚ d jq ∈ modularFunctionFieldFull N :=
  subset_adjoin ℚ _ (mem_divisorExpansions N hd)

theorem modularFunctionField_le_full :
    modularFunctionField N ≤ modularFunctionFieldFull N := by
  rw [modularFunctionField, adjoin_le_iff]
  rintro x (rfl | rfl)
  · have h := jqd_mem_full N (one_dvd N)
    rwa [qExpand_one_apply] at h
  · exact jqd_mem_full N dvd_rfl

theorem full_degeneracy_le {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) :
    modularFunctionFieldFull N ≤ modularFunctionFieldFull M := by
  rw [modularFunctionFieldFull, adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  haveI := hne
  exact jqd_mem_full M (hdvd.trans h)

omit [NeZero N] in

theorem full_degeneracy_map_le (ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldFull N).map (qExpandₐ ℓ) ≤ modularFunctionFieldFull (N * ℓ) := by
  rw [modularFunctionFieldFull, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hne, hdvd, rfl⟩, rfl⟩
  haveI := hne
  haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
  show qExpandₐ ℓ (qExpand ℚ d jq) ∈ _
  rw [qExpandₐ_apply, qExpand_qExpand]
  exact jqd_mem_full (N * ℓ) ((mul_dvd_mul_left ℓ hdvd).trans (dvd_of_eq (mul_comm ℓ N)))

theorem qExpandₐ_comp (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] :
    (qExpandₐ ℓ).comp (qExpandₐ ℓ') = qExpandₐ (ℓ * ℓ') := by
  refine AlgHom.ext fun f => ?_
  simp only [AlgHom.comp_apply, qExpandₐ_apply]
  exact qExpand_qExpand ℓ' ℓ f

end AllDivisors

end ModularCurve
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
