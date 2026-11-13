/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

Declaration-level adaptation of TauCeti revision
 a6027b1d24fcb935c53bd5b50d11b40991cda418,
RingTheory/DedekindDomain/Different/Localization.lean.
The localized integral-closure property is supplied by the proved
IntegralClosureLocalization module, not an assumed local different comparison.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.IntegralClosureLocalization
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The genuine different under simultaneous base localization

This compares the actual differents in the same fraction-field extension.
The extension ring must localize at the image of the very same base submonoid.
UniqueLocalization supplies this condition for a single prime only when the
prime above the base prime is genuinely unique.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open Module
open scoped nonZeroDivisors

namespace GlobalDifferentTransport

section TraceDual

variable {R Rₘ S Sₘ K L : Type*}
  [CommRing R] [CommRing Rₘ] [CommRing S] [CommRing Sₘ] [Field K] [Field L]
  [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ]
  [Algebra R K] [Algebra Rₘ K] [IsScalarTower R Rₘ K]
  [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L] [Algebra Sₘ L]
  [IsScalarTower R K L] [IsScalarTower Rₘ K L] [IsScalarTower R S L]
  [IsScalarTower Rₘ Sₘ L] [IsScalarTower S Sₘ L]
  {M : Submonoid R} [IsLocalization M Rₘ] [Module.Finite R S]

/-- One base denominator clears the traces against every global integral element, because the
global integral algebra is a finite module. -/
private theorem exists_smul_mem_traceDual_of_mem_traceDual {x : L}
    (hx : x ∈ Submodule.traceDual Rₘ K (1 : Submodule Sₘ L)) :
    ∃ b : M, algebraMap R K b • x ∈ Submodule.traceDual R K (1 : Submodule S L) := by
  rw [Submodule.mem_traceDual] at hx
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  choose c hc using fun i : s ↦ hx (algebraMap S L i) (Submodule.mem_one.mpr
    ⟨algebraMap S Sₘ i, by rw [← IsScalarTower.algebraMap_apply S Sₘ L]⟩)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M c
  refine ⟨b, ?_⟩
  rw [Submodule.mem_traceDual]
  intro a ha
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp ha
  let f : S →ₗ[R] K := ((Algebra.traceForm K L) (algebraMap R K b • x)).restrictScalars R
    ∘ₗ (Algebra.linearMap S L).restrictScalars R
  let N : Submodule R S := Submodule.comap f (1 : Submodule R K)
  have hsN : (s : Set S) ⊆ N := by
    intro i hi
    let j : s := ⟨i, hi⟩
    obtain ⟨r, hr⟩ := hb j
    apply Submodule.mem_comap.mpr
    rw [Submodule.mem_one]
    refine ⟨r, ?_⟩
    calc
      algebraMap R K r = algebraMap Rₘ K (algebraMap R Rₘ r) := by
        rw [IsScalarTower.algebraMap_apply R Rₘ K]
      _ = algebraMap Rₘ K ((b : R) • c j) := congrArg (algebraMap Rₘ K) hr
      _ = algebraMap R K b * algebraMap Rₘ K (c j) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R Rₘ K]
      _ = algebraMap R K b * (Algebra.traceForm K L x) (algebraMap S L j) := by rw [hc j]
      _ = (Algebra.trace K L) (algebraMap R K b • (x * algebraMap S L j)) := by
        rw [(Algebra.trace K L).map_smul, Algebra.traceForm_apply, Algebra.smul_def]
        simp only [Algebra.algebraMap_self_apply]
      _ = (Algebra.trace K L) ((algebraMap R K b • x) * algebraMap S L i) := by
        congr 1
        simp only [Algebra.smul_def, j]
        ring
      _ = ((Algebra.traceForm K L) (algebraMap R K b • x)) (algebraMap S L i) := by
        rw [Algebra.traceForm_apply]
      _ = f i := by
        simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Algebra.linearMap_apply]
  have hN : N = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Submodule.span_le.mpr hsN
  exact Submodule.mem_one.mp (Submodule.mem_comap.mp (hN.symm ▸ Submodule.mem_top : a ∈ N))

variable [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Sₘ L]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

include M in
/-- The actual integral trace dual commutes with simultaneous localization of a finite algebra. -/
theorem span_traceDual_one_baseLocalization :
    Submodule.span Sₘ (Submodule.traceDual R K (1 : Submodule S L) : Set L) =
      Submodule.traceDual Rₘ K (1 : Submodule Sₘ L) := by
  let _ : Nontrivial R := (algebraMap R K).domain_nontrivial
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe] at hx ⊢
    rw [Submodule.mem_traceDual] at hx ⊢
    intro a ha
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨⟨s, _, m, hm, rfl⟩, hsm⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid S M) a
    obtain ⟨r, hr⟩ := hx (algebraMap S L s) (Submodule.mem_one.mpr ⟨s, rfl⟩)
    have hsmL : algebraMap Sₘ L a * algebraMap R L m = algebraMap S L s := by
      simpa only [map_mul, IsScalarTower.algebraMap_apply R S Sₘ,
        IsScalarTower.algebraMap_apply R Sₘ L,
        IsScalarTower.algebraMap_apply S Sₘ L] using congrArg (algebraMap Sₘ L) hsm
    have htrace : (Algebra.traceForm K L x) (algebraMap Sₘ L a) * algebraMap R K m =
        algebraMap R K r := by
      calc
        _ = algebraMap R K m * (Algebra.trace K L) (x * algebraMap Sₘ L a) := mul_comm _ _
        _ = (Algebra.trace K L) (algebraMap R K m • (x * algebraMap Sₘ L a)) :=
          ((Algebra.trace K L).map_smul _ _).symm
        _ = (Algebra.trace K L) (x * algebraMap S L s) := by
          congr 1
          rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L]
          calc
            algebraMap R L m * (x * algebraMap Sₘ L a) =
                x * (algebraMap Sₘ L a * algebraMap R L m) := by ring
            _ = x * algebraMap S L s := by rw [hsmL]
        _ = _ := hr.symm
    refine ⟨IsLocalization.mk' Rₘ r ⟨m, hm⟩, ?_⟩
    apply mul_right_cancel₀ (b := algebraMap R K m)
    · rw [IsScalarTower.algebraMap_apply R Rₘ K]
      exact ((IsLocalization.map_units Rₘ ⟨m, hm⟩).map (algebraMap Rₘ K)).ne_zero
    rw [IsScalarTower.algebraMap_apply R Rₘ K, ← map_mul, IsLocalization.mk'_spec]
    simpa only [IsScalarTower.algebraMap_apply R Rₘ K] using htrace.symm
  · intro x hx
    obtain ⟨b, hbx⟩ := exists_smul_mem_traceDual_of_mem_traceDual
      (R := R) (Rₘ := Rₘ) (S := S) (Sₘ := Sₘ) (K := K) (L := L) (M := M) hx
    let bm : Algebra.algebraMapSubmonoid S M := ⟨algebraMap R S b, ⟨b, b.2, rfl⟩⟩
    have hbx' := Submodule.smul_mem (Submodule.span Sₘ
      (Submodule.traceDual R K (1 : Submodule S L) : Set L)) (IsLocalization.mk' Sₘ 1 bm)
      (Submodule.subset_span hbx)
    suffices IsLocalization.mk' Sₘ 1 bm • (algebraMap R K b • x) = x by rwa [this] at hbx'
    rw [Algebra.smul_def, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R S L, IsScalarTower.algebraMap_apply S Sₘ L,
      ← mul_assoc, ← map_mul, IsLocalization.mk'_spec]
    simp only [map_one, one_mul]

end TraceDual

section Different

variable {R Rₘ S Sₘ K L : Type*}
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDedekindDomain S] [CommRing Rₘ] [IsDomain Rₘ] [IsIntegrallyClosed Rₘ]
  [CommRing Sₘ] [IsDedekindDomain Sₘ] [Field K] [Field L]
  [Algebra R Rₘ] [Algebra R S] [Algebra Rₘ Sₘ] [Algebra S Sₘ]
  [Algebra R K] [IsFractionRing R K] [Algebra Rₘ K] [IsFractionRing Rₘ K]
  [IsScalarTower R Rₘ K]
  [Algebra K L] [Algebra R L] [Algebra Rₘ L] [Algebra S L] [IsFractionRing S L]
  [Algebra Sₘ L] [IsScalarTower R K L] [IsScalarTower Rₘ K L]
  [IsScalarTower R S L] [IsScalarTower Rₘ Sₘ L] [IsScalarTower S Sₘ L]
  [Algebra R Sₘ] [IsScalarTower R S Sₘ] [IsScalarTower R Sₘ L] [IsScalarTower R Rₘ L]
  [IsIntegralClosure S R L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Module.Finite R S] [Module.IsTorsionFree R S] [Module.IsTorsionFree Rₘ Sₘ]
  {M : Submonoid R} [IsLocalization M Rₘ]
  [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

include K L M in
/-- The genuine different ideal commutes with simultaneous base localization.
The localized integral-closure property is proved here; only the structural localized
DVR/domain/fraction-field properties and the compatible maps are required as inputs. -/
theorem map_differentIdeal_baseLocalization (hM : M ≤ R⁰) :
    (differentIdeal R S).map (algebraMap S Sₘ) = differentIdeal Rₘ Sₘ := by
  have hMS : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (algebraMap_injective_of_field_isFractionRing R S K L) hM
  let : IsFractionRing Sₘ L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid S M) Sₘ L
  let : IsIntegralClosure Sₘ Rₘ L := isIntegralClosure_baseLocalization (S := S) (K := K) hM
  have hSSₘ : Function.Injective (algebraMap S Sₘ) := IsLocalization.injective Sₘ hMS
  let h : S⁰ ≤ Submonoid.comap (algebraMap S Sₘ) Sₘ⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hSSₘ
  have hdual : (FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)).extended L h =
      FractionalIdeal.dual Rₘ K (1 : FractionalIdeal Sₘ⁰ L) := by
    apply FractionalIdeal.coeToSubmodule_injective
    refine (FractionalIdeal.coe_extended_eq_span L h _).trans ?_
    have hmap : IsLocalization.map L (algebraMap S Sₘ) h = RingHom.id L := by
      apply IsFractionRing.ringHom_ext (A := S)
      intro s
      rw [IsLocalization.map_eq, RingHom.id_apply, IsScalarTower.algebraMap_apply S Sₘ L]
    rw [hmap]
    simp only [RingHom.id_apply, Set.image_id']
    have hset : ((FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Set L) =
        (Submodule.traceDual R K (1 : Submodule S L) : Set L) := by
      ext x
      rw [SetLike.mem_coe, SetLike.mem_coe, ← FractionalIdeal.mem_coe,
        FractionalIdeal.coe_dual_one]
    rw [hset, FractionalIdeal.coe_dual_one]
    exact span_traceDual_one_baseLocalization (M := M)
  rw [← FractionalIdeal.coeIdeal_inj (K := L),
    ← FractionalIdeal.extended_coeIdeal_eq_map (K := L) L h,
    ← FractionalIdeal.extendedHom'_apply,
    coeIdeal_differentIdeal R K L S, coeIdeal_differentIdeal Rₘ K L Sₘ,
    map_inv₀, FractionalIdeal.extendedHom'_apply, hdual]

end Different

end GlobalDifferentTransport
