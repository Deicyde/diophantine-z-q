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
  Source file    : P2M/Sol/S_ModularCurve_map_intCast_pow_char_eq_qExpand.lean
  Source sha256  : 0d586779db60722e98fae9a5a76ddaac364ec7bc038846866b1a3782a7cfc48d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T1×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_ModularCurve_X0
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand
r2nos_namespace_dual

noncomputable section

open scoped PowerSeries.WithPiTopology
r2nos_open_scoped_dual "PowerSeries.WithPiTopology"
open PowerSeries HahnSeries
r2nos_open_dual "PowerSeries HahnSeries"

namespace ModularCurve
r2nos_namespace_dual
w03_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single ofPowerSeries_coeff_of_neg"
w03_open "ModularCurve"

namespace CharL
r2nos_namespace_dual

section LaurentMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def laurentMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one (R := R) (S := S) f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul (R := R) (S := S) f.toNonUnitalRingHom
  map_zero' := by
    ext k
    show f ((0 : LaurentSeries R).coeff k) = (0 : LaurentSeries S).coeff k
    rw [HahnSeries.coeff_zero, HahnSeries.coeff_zero, map_zero]
  map_add' x y := by
    ext k
    show f ((x + y).coeff k) = (x.map f + y.map f).coeff k
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, map_add]
    rfl

theorem laurentMap_apply (f : R →+* S) (x : LaurentSeries R) : laurentMap f x = x.map f := rfl

@[scoped simp]
theorem laurentMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (laurentMap f x).coeff k = f (x.coeff k) := rfl

@[scoped simp]
theorem laurentMap_single (f : R →+* S) (k : ℤ) (r : R) :
    laurentMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext g
  rw [laurentMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
    map_zero]

theorem laurentMap_ofPowerSeries (f : R →+* S) (p : PowerSeries R) :
    laurentMap f (HahnSeries.ofPowerSeries ℤ R p) =
      HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [laurentMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem laurentMap_qExpand (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    laurentMap f (qExpand R N x) = qExpand S N (laurentMap f x) := by
  ext k
  rw [laurentMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, laurentMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N x hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

end LaurentMap

section ExpandSeam

variable {R : Type*} [CommRing R] (p : ℕ) [NeZero p]

theorem qExpand_ofPowerSeries_eq_expand (u : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) u) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hpm : (p : ℤ) * m < 0 := mul_neg_of_pos_of_neg hp0 hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hpm]
    · lift m to ℕ using hm with m
      have hcast : ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) := by push_cast; ring
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcast, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hpk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_of_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd p (NeZero.ne p) u
          (fun ⟨m, hm⟩ => hpk ⟨m, by exact_mod_cast hm⟩)]

end ExpandSeam

section KeyLemma

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

theorem pow_char_single_one_eq (n : ℤ) :
    (HahnSeries.single n (1 : R)) ^ p
      = laurentMap (frobenius R p) (qExpand R p (HahnSeries.single n (1 : R))) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [HahnSeries.single_pow, one_pow, qExpand_single, laurentMap_single,
    show frobenius R p 1 = 1 from (frobenius R p).map_one,
    show (p • n : ℤ) = (p : ℤ) * n from nsmul_eq_mul p n]

theorem pow_char_ofPowerSeries_eq (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u) ^ p
      = laurentMap (frobenius R p)
          (qExpand R p (HahnSeries.ofPowerSeries ℤ R u)) := by
  haveI : ExpChar R p := ExpChar.prime (Fact.out : p.Prime)
  rw [qExpand_ofPowerSeries_eq_expand p u, laurentMap_ofPowerSeries, ← map_pow]
  congr 1
  exact (MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u)).symm

theorem pow_char_eq_laurentMap_frobenius_qExpand (s : LaurentSeries R) :
    s ^ p = laurentMap (frobenius R p) (qExpand R p s) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  conv_rhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart s]
  rw [mul_pow, map_mul, map_mul, pow_char_single_one_eq p s.order]
  congr 1
  exact pow_char_ofPowerSeries_eq p s.powerSeriesPart

theorem pow_char_eq_qExpand_of_coeff_fixed (s : LaurentSeries R)
    (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) :
    s ^ p = qExpand R p s := by
  rw [pow_char_eq_laurentMap_frobenius_qExpand p s]
  ext k
  rw [laurentMap_coeff, frobenius_def]
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul, hfix m]
  · rw [qExpand_coeff_of_not_dvd p _ hpk, zero_pow (Fact.out : p.Prime).ne_zero]

end KeyLemma

section IntCastImage

variable {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

theorem intCast_pow_char_eq (n : ℤ) : ((n : K) : K) ^ ℓ = (n : K) := by
  haveI : ExpChar K ℓ := ExpChar.prime (Fact.out : ℓ.Prime)
  have h : (frobenius K ℓ).comp (Int.castRingHom K) = Int.castRingHom K :=
    RingHom.ext_int _ _
  calc ((n : K) : K) ^ ℓ = frobenius K ℓ (Int.castRingHom K n) := rfl
    _ = ((frobenius K ℓ).comp (Int.castRingHom K)) n := rfl
    _ = Int.castRingHom K n := by rw [h]
    _ = (n : K) := rfl

theorem pow_char_laurentMap_intCast_eq_qExpand (sInt : LaurentSeries ℤ) :
    (laurentMap (Int.castRingHom K) sInt) ^ ℓ
      = qExpand K ℓ (laurentMap (Int.castRingHom K) sInt) :=
  pow_char_eq_qExpand_of_coeff_fixed ℓ (laurentMap (Int.castRingHom K) sInt)
    fun k => by rw [laurentMap_coeff]; exact intCast_pow_char_eq ℓ (sInt.coeff k)

end IntCastImage

end CharL
w03_reactivate "P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve.CharL"

end ModularCurve
w03_reactivate "P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve.CharL P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve"

end
w03_reactivate "P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve.CharL P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve"

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.ModularCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.ModularCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_ModularCurve_map_intCast_pow_char_eq_qExpand.ModularCurve" in
theorem solution {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (s : LaurentSeries ℤ) :
    (s.map (Int.castRingHom K)) ^ ℓ = qExpand K ℓ (s.map (Int.castRingHom K)) :=
  ModularCurve.CharL.pow_char_laurentMap_intCast_eq_qExpand ℓ s
end S_ModularCurve_map_intCast_pow_char_eq_qExpand
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
