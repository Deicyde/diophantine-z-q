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
  Source file    : P2M/Sol/S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero.lean
  Source sha256  : 1c56dbe60be4ee4bdc258da4610b8721d9908bba0324741d701ce5cf8e340d2f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 4800000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
r2nos_namespace_dual

open Bialgebra
r2nos_open_dual "Bialgebra"


noncomputable section

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    haveI : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
      RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)) := by
  haveI hIp : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
    RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
  classical
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI
  set S := Localization.AtPrime I
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A

  obtain ⟨d, ξ, hξI, hξli, hξspan⟩ :=
    HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType K A

  have hgr : ∀ {m n : ℕ} {x y : A}, x ∈ I ^ m → x ∉ I ^ (m + 1) → y ∈ I ^ n →
      y ∉ I ^ (n + 1) → x * y ∉ I ^ (m + n + 1) := fun {m n x y} hxm hxm' hyn hyn' =>
    HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
      K A hξI hξli hξspan hxm hxm' hyn hyn'

  have hsat : ∀ {x y : A}, x ∉ I → ∀ N, x * y ∈ I ^ N → y ∈ I ^ N := by
    intro x y hx N hxy
    by_contra hyn
    have hne : ∃ j, y ∉ I ^ j := ⟨N, hyn⟩
    set m₀ := Nat.find hne
    have hym₀ : y ∉ I ^ m₀ := Nat.find_spec hne
    have hm₀N : m₀ ≤ N := Nat.find_le hyn
    have hm₀pos : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) hym₀
      · exact hp
    have hym₀' : y ∈ I ^ (m₀ - 1) :=
      not_not.mp (Nat.find_min hne (show m₀ - 1 < m₀ by omega))
    have hx0 : x ∈ I ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact trivial
    have hx1 : x ∉ I ^ (0 + 1) := by rwa [zero_add, pow_one]
    have hym₀'' : y ∉ I ^ (m₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hm₀pos]
    have hnot : x * y ∉ I ^ (0 + (m₀ - 1) + 1) := hgr hx0 hx1 hym₀' hym₀''
    exact hnot (Ideal.pow_le_pow_right (by omega) hxy)

  have hKrullW : ∀ a : A, algebraMap A S a ≠ 0 → ∃ n, a ∉ I ^ n := by
    intro a ha
    set J := I.map (algebraMap A S) with hJ
    have hJmax : J = IsLocalRing.maximalIdeal S := by
      rw [hJ]; exact Localization.AtPrime.map_eq_maximalIdeal
    have hJne : J ≠ ⊤ := hJmax ▸ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    have hKrull : ⨅ n, J ^ n = ⊥ := J.iInf_pow_eq_bot_of_isLocalRing hJne
    have hnotbot : algebraMap A S a ∉ (⊥ : Ideal S) := by simpa [Ideal.mem_bot] using ha
    rw [← hKrull, Ideal.mem_iInf] at hnotbot
    simp only [not_forall] at hnotbot
    obtain ⟨n, hn⟩ := hnotbot
    exact ⟨n, fun han => hn (by rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ han)⟩

  have hNZD : ∀ z w : S, z * w = 0 → z = 0 ∨ w = 0 := by
    intro z w hzw
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hz, hw⟩ := hc
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl z
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl w
    rw [← IsLocalization.mk'_mul] at hzw
    obtain ⟨u, hu⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzw
    have hab_all : ∀ N, a * b ∈ I ^ N := fun N =>
      hsat u.2 N (by rw [hu]; exact Ideal.zero_mem _)
    have haφ : algebraMap A S a ≠ 0 := fun h0 => hz <| by
      have hspec := IsLocalization.mk'_spec S a s
      rw [h0] at hspec
      exact (IsLocalization.map_units S s).mul_left_eq_zero.mp hspec
    have hbφ : algebraMap A S b ≠ 0 := fun h0 => hw <| by
      have hspec := IsLocalization.mk'_spec S b t
      rw [h0] at hspec
      exact (IsLocalization.map_units S t).mul_left_eq_zero.mp hspec
    obtain ⟨m, hm⟩ := hKrullW a haφ
    obtain ⟨n, hn⟩ := hKrullW b hbφ
    have hnea : ∃ j, a ∉ I ^ j := ⟨m, hm⟩
    have hneb : ∃ j, b ∉ I ^ j := ⟨n, hn⟩
    set m₀ := Nat.find hnea
    set n₀ := Nat.find hneb
    have ham₀ : a ∉ I ^ m₀ := Nat.find_spec hnea
    have hbn₀ : b ∉ I ^ n₀ := Nat.find_spec hneb
    have hm₀pos : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) ham₀
      · exact hp
    have hn₀pos : 1 ≤ n₀ := by
      rcases Nat.eq_zero_or_pos n₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) hbn₀
      · exact hp
    have ham₀' : a ∈ I ^ (m₀ - 1) :=
      not_not.mp (Nat.find_min hnea (show m₀ - 1 < m₀ by omega))
    have hbn₀' : b ∈ I ^ (n₀ - 1) :=
      not_not.mp (Nat.find_min hneb (show n₀ - 1 < n₀ by omega))
    have ham₀'' : a ∉ I ^ (m₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hm₀pos]
    have hbn₀'' : b ∉ I ^ (n₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hn₀pos]
    exact hgr ham₀' ham₀'' hbn₀' hbn₀'' (hab_all _)
  haveI : NoZeroDivisors S := ⟨fun {a b} => hNZD a b⟩
  exact { }

end
end S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
