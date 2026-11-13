/-
Finite extraction of actual global inertia generators for the Kronecker–Weber
route. This uses the closed global inertia theorem and pure finite-group facts;
no local root containment or global class-field premise is assumed.
-/
module

public import ZInQKernel.Contrib.KroneckerWeber.GlobalInertia
public import ZInQKernel.Contrib.KroneckerWeber.GlobalDegree
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A finite family of actual inertia groups generates an abelian number field

Finiteness of the set of subgroups of the finite Galois group selects finitely
many actual integer primes. The degree bound is on the ORIGINAL global extension,
with its actual ramification indices over `ℤ`. No local field or assumed
cyclotomic model is substituted for these objects.
-/

public section

set_option autoImplicit false

namespace ZInQ.Contrib.KroneckerWeber

open NumberField IsDedekindDomain
open scoped NumberField IsMulCommutative

/-- Actual global inertia cardinality equals the original rational ramification
index, with the original integer scalar map and Galois action. -/
theorem card_global_inertia_eq_ramificationIdx
    (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
    (P : Ideal (𝓞 M)) [P.IsPrime] :
    Nat.card (P.inertia (M ≃ₐ[ℚ] M)) = P.ramificationIdx ℤ := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn (P.under ℤ) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (M ≃ₐ[ℚ] M)]

/-- Select finitely many ACTUAL integer primes whose inertia subgroups generate
the entire original Galois group. No class-field premise or given generator
family is needed; the full global theorem and finite subgroup set supply it. -/
theorem exists_finset_global_inertia_generating
    (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M] :
    ∃ s : Finset (HeightOneSpectrum (𝓞 M)),
      (⨆ P ∈ s, P.asIdeal.inertia (M ≃ₐ[ℚ] M)) = ⊤ := by
  classical
  let I (P : HeightOneSpectrum (𝓞 M)) : Subgroup (M ≃ₐ[ℚ] M) :=
    P.asIdeal.inertia (M ≃ₐ[ℚ] M)
  let J : Set (Subgroup (M ≃ₐ[ℚ] M)) := Set.range I
  have hJ : J.Finite := Set.toFinite _
  have : Fintype J := hJ.fintype
  choose pick hpick using fun H : J => H.property
  let s : Finset (HeightOneSpectrum (𝓞 M)) := Finset.univ.image pick
  refine ⟨s, top_unique ?_⟩
  rw [← globalInertiaSpan_eq_top M, globalInertiaSpan_def]
  refine iSup_le fun P => ?_
  let H : J := ⟨I P, ⟨P, rfl⟩⟩
  have hmem : pick H ∈ s := Finset.mem_image.mpr ⟨H, Finset.mem_univ _, rfl⟩
  change I P ≤ ⨆ P ∈ s, I P
  have heq : I (pick H) = I P := hpick H
  rw [← heq]
  exact le_iSup_of_le (pick H) (le_iSup_of_le hmem le_rfl)

/-- The global Galois degree of EVERY abelian number field is bounded by a finite
product of its actual integer-prime ramification indices. Local cyclotomic
inertia bounds needed by full Kronecker–Weber are not asserted here. -/
theorem exists_global_inertia_degree_bound
    (M : Type*) [Field M] [NumberField M] [IsAbelianGalois ℚ M] :
    ∃ s : Finset (HeightOneSpectrum (𝓞 M)),
      (⨆ P ∈ s, P.asIdeal.inertia (M ≃ₐ[ℚ] M)) = ⊤ ∧
      Module.finrank ℚ M ≤ ∏ P ∈ s, P.asIdeal.ramificationIdx ℤ := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_global_inertia_generating M
  let I (P : s) : Subgroup (M ≃ₐ[ℚ] M) := P.val.asIdeal.inertia (M ≃ₐ[ℚ] M)
  have hsup : (⨆ P, I P) = ⨆ P ∈ s, P.asIdeal.inertia (M ≃ₐ[ℚ] M) := by
    apply le_antisymm
    · exact iSup_le fun P => le_iSup_of_le P.val (le_iSup_of_le P.property le_rfl)
    · exact iSup_le fun P => iSup_le fun hP => le_iSup_of_le (⟨P, hP⟩ : s) le_rfl
  have hI : (⨆ P, I P) = ⊤ := hsup.trans hs
  have hcard := card_le_prod_of_subgroup_generation I hI
  rw [IsGalois.card_aut_eq_finrank] at hcard
  refine ⟨s, hs, ?_⟩
  calc
    Module.finrank ℚ M ≤ ∏ P : s, P.val.asIdeal.ramificationIdx ℤ := by
      simpa only [I, card_global_inertia_eq_ramificationIdx] using hcard
    _ = ∏ P ∈ s, P.asIdeal.ramificationIdx ℤ :=
      (Finset.prod_subtype s (fun _ => Iff.rfl)
        (fun P : HeightOneSpectrum (𝓞 M) => P.asIdeal.ramificationIdx ℤ)).symm

end ZInQ.Contrib.KroneckerWeber
