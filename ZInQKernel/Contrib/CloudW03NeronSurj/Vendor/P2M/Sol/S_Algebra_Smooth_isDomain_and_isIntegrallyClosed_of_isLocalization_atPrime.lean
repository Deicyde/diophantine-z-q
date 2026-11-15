/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 2 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
set_option autoImplicit false
universe u

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ := by
  classical
  have hp : p.IsPrime := inferInstance

  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  set Sf := Localization.Away f with hSf
  haveI : Algebra.IsStandardSmooth R Sf := hstd

  obtain ⟨ι, σ, hσ, hι, ⟨Pr⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R Sf).out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension R Sf := ⟨ι, σ, hσ, hι, Pr, rfl⟩
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial Pr.dimension R Sf
  letI : Algebra (MvPolynomial (Fin Pr.dimension) R) Sf := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) R) Sf := hg

  have hdisj : Disjoint (Submonoid.powers f : Set S) (p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  set q : Ideal Sf := p.map (algebraMap S Sf) with hq
  haveI hqp : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Sf p hp hdisj
  have hcomap : q.comap (algebraMap S Sf) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f) Sf hp hdisj

  have hunit : IsUnit (algebraMap S Sₚ f) := IsLocalization.map_units Sₚ (⟨f, hf⟩ : p.primeCompl)
  letI : Algebra Sf Sₚ := (IsLocalization.Away.lift f hunit).toAlgebra
  haveI : IsScalarTower S Sf Sₚ := IsScalarTower.of_algebraMap_eq fun s => by
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_eq]
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro _ ⟨k, rfl⟩
    exact fun h => hf (hp.mem_of_pow_mem k h)
  haveI hloc : IsLocalization (p.primeCompl.map (algebraMap S Sf)) Sₚ :=
    IsLocalization.isLocalization_of_submonoid_le Sf Sₚ (Submonoid.powers f) p.primeCompl hle
  haveI : IsLocalization.AtPrime Sₚ q := by
    refine IsLocalization.of_le_of_exists_dvd (p.primeCompl.map (algebraMap S Sf)) q.primeCompl ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      change algebraMap S Sf s ∉ q
      intro h
      exact hs (by rw [← hcomap]; exact h)
    · intro n hn
      obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) n
      have hm : (m : S) ∉ p := Set.disjoint_left.mp hdisj m.2
      have hs : s ∉ p := by
        intro hs
        apply hn
        have hspec : IsLocalization.mk' Sf s m * algebraMap S Sf m = algebraMap S Sf s :=
          IsLocalization.mk'_spec Sf s m
        have hmem : algebraMap S Sf s ∈ q := Ideal.mem_map_of_mem _ hs
        rw [← hspec] at hmem
        rcases hqp.mem_or_mem hmem with h | h
        · exact h
        · exact absurd (show (m : S) ∈ p by rw [← hcomap]; exact h) hm
      exact ⟨algebraMap S Sf s, ⟨s, hs, rfl⟩, algebraMap S Sf m, (IsLocalization.mk'_spec Sf s m).symm⟩
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (MvPolynomial (Fin Pr.dimension) R) Sf q Sₚ

end P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

end ZInQ.Contrib.CloudW03NeronSurj.FLT
