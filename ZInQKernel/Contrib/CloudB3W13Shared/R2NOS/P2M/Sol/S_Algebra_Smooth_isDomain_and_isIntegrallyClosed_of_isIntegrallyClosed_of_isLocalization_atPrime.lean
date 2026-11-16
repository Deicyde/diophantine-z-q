/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean
  Retrieved      : 2026-11-16 (immutable raw blob at the revision above; bytes and sha256 in
                   `ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/PORT_MANIFEST.md`)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(Cloud Batch 3 Worker 13 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
2026-11-16). The changes are mechanical; no statement, hypothesis, definition or proof term was
weakened or omitted unless listed under "manual repairs":
  * the whole file is wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end`, so the
    source's root declarations become `ZInQ.Contrib.CloudW03NeronSurj.FLT.<name>`;
  * the source's `import P2M.Util` is dropped: this port contains no port commands, no local
    notation, no macro and no elaborator. Each source `p2m_*` command is replaced by the ordinary
    Lean it abbreviated (`p2m_open` by `open`, `p2m_exact_reverting @X` by the application of `X`);
  * internal `import`s are retargeted to the ported modules;
  * references to ported declarations of other modules are written with their full
    `ZInQ.Contrib.CloudW03NeronSurj.FLT.` names, since the port prefix is not opened here;
  * file-level `set_option`s reproduce the source build environment (source lakefile.lean
    leanOptions: autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000,
    backward.isDefEq.respectTransparency.types false) together with
    backward.isDefEq.respectTransparency.instanceSearchTypes false, a Lean 4.35 option absent from
    the source's Lean 4.33.1 whose `false` value restores the 4.33.1 behaviour;
  * scopes the source leaves open at end of file are closed explicitly (no-op).
Manual repairs: none.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime

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
  exact _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (MvPolynomial (Fin Pr.dimension) R) Sf q Sₚ

end P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime

end ZInQ.Contrib.CloudW03NeronSurj.FLT
