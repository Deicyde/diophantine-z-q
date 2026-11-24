/-
NOS-CORE PROBE STAGING COPY (lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean
  Source sha256  : 9fc49b7791872824aa775aa4e71b3bf5932d7c36d7a6fcb1ef15f071c6ac21ff
  Retrieved      : pinned upstream source revision (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
r2nos_namespace_dual
set_option autoImplicit false
universe u

theorem isIntegrallyClosed_mvPolynomial_fin (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) R)
  | 0 => IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | n + 1 => by
      haveI := isIntegrallyClosed_mvPolynomial_fin R n
      exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
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
  haveI : IsIntegrallyClosed (MvPolynomial (Fin Pr.dimension) R) := isIntegrallyClosed_mvPolynomial_fin R Pr.dimension
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (MvPolynomial (Fin Pr.dimension) R) Sf q Sₚ
end S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
