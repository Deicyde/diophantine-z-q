/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RingTheory.Polynomial.Distinguished), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RingTheory.Polynomial.Distinguished`.
module

public import ZInQKernel.Contrib.TauCeti.RingTheory.Polynomial.Distinguished
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

public section

section
namespace Polynomial.IsDistinguishedAt

variable {O : Type*} [CommRing O] {I : Ideal O} {F : O[X]} {p e : ℕ}

/-- If `F` is distinguished at `I` and `I ^ e ⊆ (p)`, then every root `t` of `F` in an `O`-algebra
satisfies `p ∣ t ^ (deg F * e)`. -/
theorem natCast_dvd_pow_of_aeval_eq_zero (hF : F.IsDistinguishedAt I)
    (hI : I ^ e ≤ Ideal.span {(p : O)}) {S : Type*} [CommRing S] [Algebra O S] {t : S}
    (ht : aeval t F = 0) : (p : S) ∣ t ^ (F.natDegree * e) := by
  have h := hF.toIsWeaklyEisensteinAt.pow_natDegree_le_of_aeval_zero_of_monic_mem_map ht
    hF.monic F.natDegree natDegree_map_le
  have h' : t ^ (F.natDegree * e) ∈ (Ideal.span {(p : O)}).map (algebraMap O S) := by
    rw [pow_mul]
    exact Ideal.map_mono hI (Ideal.map_pow (algebraMap O S) I e ▸ Ideal.pow_mem_pow h e)
  rwa [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton] at h'

end Polynomial.IsDistinguishedAt
end

end
