/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RingTheory.ClassGroup.HeightOneSpectrum), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RingTheory.ClassGroup.HeightOneSpectrum`.
module

public import ZInQKernel.Contrib.TauCeti.RingTheory.ClassGroup.HeightOneSpectrum
public import ZInQKernel.Contrib.TauCeti.RingTheory.ClassGroup.Basic
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.Factorization

public section

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- With a finite class group, every finite set `S₀` of height one primes is contained in a finite
set `S` whose classes generate the class group and which contains every prime containing a given
nonzero element `a`. -/
lemma _root_.ClassGroup.exists_finset_superset_closure_classGroupMk_image_eq_top
    [Finite (ClassGroup R)] (S₀ : Finset (HeightOneSpectrum R)) {a : R} (ha : a ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum R), S₀ ⊆ S ∧
      Subgroup.closure (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum R))) = ⊤ ∧
      ∀ v : HeightOneSpectrum R, a ∈ v.asIdeal → v ∈ S := by
  classical
  obtain ⟨T, hT, hgen⟩ := ClassGroup.exists_finite_closure_classGroupMk_image_eq_top (R := R)
  have ha0 : Ideal.span ({a} : Set R) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  refine ⟨S₀ ∪ hT.toFinset ∪ (Ideal.finite_factors ha0).toFinset,
    fun v hv ↦ by simp [hv], ?_, fun v hv ↦ ?_⟩
  · exact top_unique (hgen ▸ Subgroup.closure_mono (Set.image_mono fun v hv ↦ by simp [hv]))
  · simp [hv]

end

end
