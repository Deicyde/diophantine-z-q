/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 2 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * one `w03_open "IsLocalRing"` inserted after the port namespace: this file `open`s `IsLocalRing`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "IsLocalRing"

namespace P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes

open IsLocalRing

namespace Ws10Flat

theorem colon_bot_quotient_mk_eq {B : Type*} [CommRing B] (I : Ideal B) (y : B) :
    (⊥ : Submodule B (B ⧸ I)).colon {Ideal.Quotient.mk I y} = I.colon {y} := by
  ext r
  have hr : r • Ideal.Quotient.mk I y = Ideal.Quotient.mk I (r * y) := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
  rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot, hr,
    Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]

section Global

variable {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

theorem isDiscreteValuationRing_localization_of_mem_associatedPrimes
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  classical
  set Bp := Localization.AtPrime P
  have hle := P.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed Bp := isIntegrallyClosed_of_isLocalization Bp P.primeCompl hle
  have hinj : Function.Injective (algebraMap B Bp) := IsLocalization.injective Bp hle

  have hP' : IsAssociatedPrime P (B ⧸ Ideal.span {x}) := hP
  obtain ⟨z, hz⟩ := hP'.eq_radical_colon
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hPJ : P = ((Ideal.span {x}).colon {y}).radical := by
    rw [hz, colon_bot_quotient_mk_eq]
  have hmemP : ∀ m : B, m ∈ P ↔ ∃ k : ℕ, m ^ k * y ∈ Ideal.span {x} := fun m => by
    rw [hPJ]
    simp only [Ideal.mem_radical_iff, Submodule.mem_colon_singleton, smul_eq_mul]

  have hx' : algebraMap B Bp x ≠ 0 := fun e => hx (hinj (by rw [e, map_zero]))
  suffices heq : maximalIdeal Bp =
      ((Ideal.span {algebraMap B Bp x}).colon {algebraMap B Bp y}).radical by
    refine IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes hx' ?_
    show (⊥ : Submodule Bp (Bp ⧸ Ideal.span {algebraMap B Bp x})).IsAssociatedPrime (maximalIdeal Bp)
    exact ⟨inferInstance, Ideal.Quotient.mk _ (algebraMap B Bp y),
      by rw [colon_bot_quotient_mk_eq]; exact heq⟩
  apply le_antisymm
  ·
    intro q hq
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl q
    dsimp only at hq ⊢
    have hm : m ∈ P := (IsLocalization.AtPrime.mk'_mem_maximal_iff Bp P m s).mp hq
    obtain ⟨k, hk⟩ := (hmemP m).mp hm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hk
    rw [Ideal.mem_radical_iff]
    refine ⟨k, ?_⟩
    rw [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton']
    refine ⟨IsLocalization.mk' Bp c (s ^ k), ?_⟩
    rw [← IsLocalization.mk'_one (M := P.primeCompl) Bp x,
      ← IsLocalization.mk'_one (M := P.primeCompl) Bp y, ← IsLocalization.mk'_pow,
      ← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul, hc]
  ·
    refine (Ideal.IsPrime.radical_le_iff inferInstance).mpr (IsLocalRing.le_maximalIdeal ?_)
    intro htop
    have h1 : (1 : Bp) ∈ (Ideal.span {algebraMap B Bp x}).colon {algebraMap B Bp y} := by
      rw [htop]; trivial
    rw [Submodule.mem_colon_singleton, one_smul, Ideal.mem_span_singleton'] at h1
    obtain ⟨q, hq⟩ := h1
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl q
    dsimp only at hq

    have e : algebraMap B Bp (c * x) = algebraMap B Bp (s * y) := by
      rw [map_mul, map_mul, ← hq, ← IsLocalization.mk'_spec Bp c s]
      ring
    have e' : c * x = ↑s * y := hinj e
    have hsP : (s : B) ∈ P := (hmemP s).mpr ⟨1, by rw [pow_one, ← e']; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)⟩
    exact s.2 hsP

end Global

end Ws10Flat

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime P) :=
  Ws10Flat.isDiscreteValuationRing_localization_of_mem_associatedPrimes hx P hP

end P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes

end ZInQ.Contrib.CloudW03NeronSurj.FLT
