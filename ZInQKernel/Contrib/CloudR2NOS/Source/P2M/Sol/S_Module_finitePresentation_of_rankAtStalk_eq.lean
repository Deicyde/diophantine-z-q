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
  Source file    : P2M/Sol/S_Module_finitePresentation_of_rankAtStalk_eq.lean
  Source sha256  : 43ba6a9c97a0399b3aaaba939d5b1925c85a378b3e44bb61b0831348993e23af
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Module_finitePresentation_of_rankAtStalk_eq
r2nos_namespace_dual

set_option autoImplicit false

universe u v

open Module
r2nos_open_dual "Module"

namespace FPRank
r2nos_namespace_dual

section localizedTop

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] {M : Type*} [AddCommGroup M] [Module R M] {Mₛ : Type*}
  [AddCommGroup Mₛ] [Module R Mₛ] [Module A Mₛ] [IsScalarTower R A Mₛ] (f : M →ₗ[R] Mₛ)
  [IsLocalizedModule S f]

theorem localized'_eq_top_iff (N : Submodule R M) :
    N.localized' A S f = ⊤ ↔ ∀ x : M, ∃ t : S, (t : R) • x ∈ N := by
  constructor
  · intro H x
    have hx : f x ∈ N.localized' A S f := H ▸ Submodule.mem_top
    obtain ⟨m, hm, t, ht⟩ := (Submodule.mem_localized' A S f N (f x)).mp hx
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at ht
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) ht
    refine ⟨u * t, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hu]
    exact N.smul_mem _ hm
  · intro H
    refine eq_top_iff.mpr fun y _ ↦ ?_
    obtain ⟨⟨x, t⟩, hxt⟩ := IsLocalizedModule.surj S f y
    obtain ⟨t', ht'⟩ := H x
    refine (Submodule.mem_localized' A S f N y).mpr ⟨(t' : R) • x, ht', t' * t, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff, map_smul, ← hxt, Submonoid.smul_def, Submonoid.smul_def,
      Submonoid.coe_mul, mul_smul]

theorem localized'_eq_top_iff_subsingleton (N : Submodule R M) :
    N.localized' A S f = ⊤ ↔ Subsingleton (LocalizedModule S (M ⧸ N)) := by
  rw [localized'_eq_top_iff, LocalizedModule.subsingleton_iff]
  constructor
  · intro H c
    induction c using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨t, ht⟩ := H x
      exact ⟨t, t.2, by
        rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero N).mpr ht]⟩
  · intro H x
    obtain ⟨t, ht, htx⟩ := H (Submodule.Quotient.mk x)
    exact ⟨⟨t, ht⟩,
      (Submodule.Quotient.mk_eq_zero N).mp (by rw [Submodule.Quotient.mk_smul, htx])⟩

end localizedTop

section surjection

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]
  [Module.Finite A P] [Module.Flat A P] {n : ℕ}

theorem injective_of_surjective_of_rankAtStalk_eq
    (h : ∀ p : PrimeSpectrum A, rankAtStalk P p = n)
    (ψ : (Fin n → A) →ₗ[A] P) (hψ : Function.Surjective ψ) : Function.Injective ψ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · haveI : Subsingleton (Fin n → A) := inferInstance
    exact Function.injective_of_subsingleton ψ
  apply injective_of_localized_maximal
  intro J hJ
  haveI : Module.Free (Localization.AtPrime J)
      (LocalizedModule J.primeCompl (Fin n → A)) :=
    free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime J) (LocalizedModule J.primeCompl P) :=
    free_of_flat_of_isLocalRing
  have h1 : finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl (Fin n → A)) = n := by
    have := congrFun (rankAtStalk_eq_finrank_of_free (R := A) (M := Fin n → A)) ⟨J, hJ.isPrime⟩
    simpa [rankAtStalk, finrank_fin_fun] using this
  have h2 : finrank (Localization.AtPrime J) (LocalizedModule J.primeCompl P) = n :=
    h ⟨J, hJ.isPrime⟩
  let e : LocalizedModule J.primeCompl P ≃ₗ[Localization.AtPrime J]
      LocalizedModule J.primeCompl (Fin n → A) :=
    LinearEquiv.ofFinrankEq _ _ (h2.trans h1.symm)
  have hsurj : Function.Surjective (LocalizedModule.map J.primeCompl ψ) :=
    LocalizedModule.map_surjective J.primeCompl ψ hψ
  have hinj := OrzechProperty.injective_of_surjective_endomorphism
    (e.toLinearMap ∘ₗ LocalizedModule.map J.primeCompl ψ) (e.surjective.comp hsurj)
  exact fun x y hxy ↦ hinj (by simp [hxy])

theorem finitePresentation_of_surjective_of_rankAtStalk_eq
    (h : ∀ p : PrimeSpectrum A, rankAtStalk P p = n)
    (ψ : (Fin n → A) →ₗ[A] P) (hψ : Function.Surjective ψ) : Module.FinitePresentation A P := by
  haveI : Module.FinitePresentation A (Fin n → A) :=
    Module.finitePresentation_of_projective _ _
  exact Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective ψ ⟨injective_of_surjective_of_rankAtStalk_eq h ψ hψ, hψ⟩)

end surjection

section localToGlobal

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem finitePresentation_of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (H : ∀ r : s, Module.FinitePresentation (Localization.Away (r : R))
      (LocalizedModule (Submonoid.powers (r : R)) M)) :
    Module.FinitePresentation R M := by
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff π hπ, ← Module.Finite.iff_fg]
  refine Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun r : s ↦ Localization.Away (r : R))
    (Mₚ := fun r : s ↦ (LinearMap.ker π).localized' (Localization.Away (r : R))
      (Submonoid.powers (r : R))
      (LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) (Fin k → R)))
    (fun r ↦ (LinearMap.ker π).toLocalized' _ _ _) (fun r ↦ ?_)
  refine Module.Finite.iff_fg.mpr ?_
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Localization.Away (r : R))
    (Submonoid.powers (r : R)) (LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) (Fin k → R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) M) π]
  haveI := H r
  exact Module.FinitePresentation.fg_ker _
    (IsLocalizedModule.map_surjective (Submonoid.powers (r : R)) _ _ π hπ)

end localToGlobal

section mainProof

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M] {n : ℕ}

theorem exists_finitePresentation_away (h : ∀ p : PrimeSpectrum R, rankAtStalk M p = n)
    (p : PrimeSpectrum R) :
    ∃ r : R, r ∉ p.asIdeal ∧ Module.FinitePresentation (Localization.Away r)
      (LocalizedModule (Submonoid.powers r) M) := by
  classical
  let S := p.asIdeal.primeCompl
  let Rₚ := Localization.AtPrime p.asIdeal
  let f : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  haveI : Module.Free Rₚ (LocalizedModule S M) := free_of_flat_of_isLocalRing
  let b : Basis (Fin n) Rₚ (LocalizedModule S M) := Module.finBasisOfFinrankEq Rₚ _ (h p)

  choose ms hms using fun i ↦ IsLocalizedModule.surj S f (b i)
  let N : Submodule R M := Submodule.span R (Set.range fun i ↦ (ms i).1)

  have hNp : N.localized' Rₚ S f = ⊤ := by
    rw [Submodule.localized'_span, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hu : IsUnit (algebraMap R Rₚ ((ms i).2 : R)) := IsLocalization.map_units Rₚ (ms i).2
    have key : (↑(hu.unit⁻¹) : Rₚ) • f (ms i).1 = b i := by
      rw [← hms i, Submonoid.smul_def, ← algebraMap_smul Rₚ ((ms i).2 : R) (b i), smul_smul,
        IsUnit.val_inv_mul, one_smul]
    rw [SetLike.mem_coe, ← key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩)

  have hsub : Subsingleton (LocalizedModule S (M ⧸ N)) :=
    (localized'_eq_top_iff_subsingleton S Rₚ f N).mp hNp
  obtain ⟨r, hr, hrN⟩ := LocalizedModule.exists_subsingleton_away (M := M ⧸ N) p.asIdeal
  refine ⟨r, hr, ?_⟩
  let A := Localization.Away r
  let fA : M →ₗ[R] LocalizedModule (Submonoid.powers r) M :=
    LocalizedModule.mkLinearMap (Submonoid.powers r) M
  have hNA : N.localized' A (Submonoid.powers r) fA = ⊤ :=
    (localized'_eq_top_iff_subsingleton (Submonoid.powers r) A fA N).mpr hrN

  let ψ : (Fin n → A) →ₗ[A] LocalizedModule (Submonoid.powers r) M :=
    Fintype.linearCombination A fun i ↦ fA (ms i).1
  have hψ : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← top_le_iff, ← hNA,
      Submodule.localized'_span, ← Set.range_comp]
    rfl

  have hrank :
      ∀ q : PrimeSpectrum A, rankAtStalk (LocalizedModule (Submonoid.powers r) M) q = n := by
    intro q
    rw [rankAtStalk_eq_of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) M),
      rankAtStalk_baseChange]
    exact h _
  exact finitePresentation_of_surjective_of_rankAtStalk_eq hrank ψ hψ

end mainProof

section main

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M] {n : ℕ}

theorem finitePresentation_of_rankAtStalk_eq (h : ∀ p : PrimeSpectrum R, rankAtStalk M p = n) :
    Module.FinitePresentation R M := by
  choose r hr hfp using exists_finitePresentation_away (M := M) h
  refine finitePresentation_of_localizationSpan (Set.range r) ?_ ?_
  · by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  · rintro ⟨_, p, rfl⟩
    exact hfp p

end main

end FPRank

theorem solution {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) : Module.FinitePresentation R M :=
  FPRank.finitePresentation_of_rankAtStalk_eq h
end S_Module_finitePresentation_of_rankAtStalk_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
