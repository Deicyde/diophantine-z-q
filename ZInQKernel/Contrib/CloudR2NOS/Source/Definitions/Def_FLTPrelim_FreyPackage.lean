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
  Source file    : Definitions/Def_FLTPrelim_FreyPackage.lean
  Source sha256  : db451a2116b5dde045bc9ca63ca3106f1edbfe44c96929c8437436d139ce116f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.ModCases
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-
Copyright (c) 2024 Kevin Buzzard, Ruben Van de Velde, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Ported from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT, blueprint §2.5–2.6).
-/

set_option autoImplicit false

structure FreyPackage where

  a : ℤ

  b : ℤ

  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0

  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p

  hFLT : a ^ p + b ^ p = c ^ p

  hgcdab : gcd a b = 1

  ha4 : (a : ZMod 4) = 3

  hb2 : (b : ZMod 2) = 0

namespace FreyPackage
r2nos_namespace_dual

lemma hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5

lemma hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

lemma hp_odd (P : FreyPackage) : Odd P.p :=
  P.pp.odd_of_ne_two (by have := P.hp5; omega)

lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

lemma hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

lemma hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]; exact P.hFLT

lemma habc0 (P : FreyPackage) : P.a * P.b * P.c ≠ 0 :=
  mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0

lemma two_dvd_abc (P : FreyPackage) : (2 : ℤ) ∣ P.a * P.b * P.c :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
    ((ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2) _) _

def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

end FreyPackage

end ZInQ.Contrib.CloudW03NeronSurj.FLT
