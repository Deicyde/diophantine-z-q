/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Away
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
public import ZInQKernel.Contrib.TauCeti.Backport.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.Subgroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Basic
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Finite

public section
noncomputable section

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
  NumberField
open scoped NumberField nonZeroDivisors
namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Comparison of ray subgroups along a transition map**: for `𝔪 ∣ 𝔫`, the ray subgroup of `𝔪`
lies in that of `𝔫` exactly when the transition map from `𝔫` to `𝔪` is injective. Under the
surjective ray class map modulo `𝔫`, the ray subgroup of `𝔪` is the preimage of the kernel of the
transition map, and that of `𝔫` is the preimage of the trivial subgroup. -/
theorem raySubgroup_le_raySubgroup_iff {𝔪 𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) :
    raySubgroup 𝔪 ≤ raySubgroup 𝔫 ↔ (classMap h).ker ≤ ⊥ := by
  rw [← ker_rayClassQuotient, ← ker_rayClassQuotient, ← classMap_comp_rayClassQuotient h,
    ← MonoidHom.comap_ker, ← MonoidHom.comap_bot (rayClassQuotient 𝔫)]
  exact Subgroup.comap_le_comap_of_surjective (rayClassQuotient_surjective 𝔫)

end TauCeti.GlobalNumberFields
end

section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
  NumberField
open scoped NumberField nonZeroDivisors
namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **The ray class of a uniformizer at a finite place is the ray class of the prime.** For a
finite place `v` of `K` outside the support of a modulus `𝔪` and a uniformizer `π` of `K_v`, the
class of the idele with component `π` at `v` and `1` elsewhere has the ray class of the prime `v`:
this idele is congruent to one modulo `𝔪`, and its fractional ideal is `v`. -/
theorem rayClassQuotient_ofAdicCompletion_of_isUniformizer {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ 𝔪.support) {π : (v.adicCompletion K)ˣ} (hπ : IsUniformizer (v.adicCompletion K) π)
    (I : idealsPrimeTo 𝔪)
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) :
    rayClassQuotient 𝔪 (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) = rayClassMk 𝔪 I := by
  -- The idele concentrated at `v` is trivial at the places of `𝔪`.
  have hmem : IdeleGroup.ofAdicCompletion (𝓞 K) K v π ∈ ideleCongrOneSubgroup 𝔪 := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v' hv' ↦ ?_, fun w _ ↦ ?_⟩
    · have hne : v' ≠ v := fun he ↦ hv ((Modulus.mem_support_iff 𝔪 v).mpr (he ▸ hv'))
      simp [ideleFiniteCoord_ofAdicCompletion_of_ne v' hne]
    · simp [InfinitePlace.ideleInfiniteCoord_ofAdicCompletion]
  -- A uniformizer has valuation `exp (-1)`, so the fractional ideal of the idele is `v`.
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [IdeleClassGroup.ofAdicCompletion_apply, rayClassQuotient_mk_of_mem hmem]
  refine congrArg _ (Subtype.ext ?_)
  dsimp only
  rw [toFractionalIdeal_toFiniteIdele_ofAdicCompletion_of_eq_exp_neg_one v
    (v.isUniformizer_iff_valued_eq_exp_neg_one.1 hπ)]
  exact Units.ext ((coe_unitOfPrime v K).trans hI.symm)

end TauCeti.GlobalNumberFields
end

end
end
