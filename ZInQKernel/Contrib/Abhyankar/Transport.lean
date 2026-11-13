/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The Tau Ceti contributors

Modified for this contribution: ported to Mathlib v4.35.0, placed in a project
namespace, and restricted to the ramification transport needed by T2.
Source: TauCeti/RingTheory/RamificationInertia/Bijective.lean,
revision 30f41378f0cb1d569f51d8a4d0cb74aea8a80e44, declarations
`Ideal.ramificationIdx_eq_of_surjective` and `Ideal.ramificationIdx_map_algEquiv`.
-/
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Transport of the actual ramification index

These lemmas concern Mathlib's localization-length definition
`Ideal.ramificationIdx`, not an assumed valuation or an alternative index.
They do not prove Abhyankar's lemma.
-/

namespace ZInQ.Contrib.Abhyankar

open Ideal

/-- A surjective change of the base ring preserves the localization-length index. -/
theorem ramificationIdx_eq_of_surjective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (h : Function.Surjective (algebraMap R S)) (q : Ideal T) :
    q.ramificationIdx S = q.ramificationIdx R := by
  have hm : (q.under R).map (algebraMap R S) = q.under S := by
    rw [← under_under (A := R) (B := S) q]
    exact map_comap_of_surjective _ h _
  by_cases hq : q.IsPrime
  · rw [ramificationIdx_def, ramificationIdx_def,
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← map_map, hm]
  · rw [ramificationIdx_of_not_isPrime q S hq, ramificationIdx_of_not_isPrime q R hq]

/-- Changing the integral model by an actual algebra equivalence preserves ramification.
The ideal is transported by `Ideal.map`; no identification of prime sets is assumed. -/
theorem ramificationIdx_map_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) (q : Ideal S) :
    (q.map e).ramificationIdx R = q.ramificationIdx R := by
  by_cases hq : q.IsPrime
  swap
  · rw [ramificationIdx_of_not_isPrime _ _ hq, ramificationIdx_of_not_isPrime]
    intro h
    have := comap_isPrime e (K := q.map e)
    exact hq (by rwa [comap_map_of_bijective _ e.bijective] at this)
  let : Algebra S T := e.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  have hbij : Function.Bijective (algebraMap S T) := e.bijective
  have : Module.Flat S T :=
    .of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap S T) hbij).symm
  have : (q.map e).LiesOver q := ⟨(comap_map_of_bijective _ hbij).symm⟩
  have : (q.map e).IsPrime := map_isPrime_of_equiv e
  rw [ramificationIdx_tower (q := q), ← ramificationIdx_eq_of_surjective hbij.2,
    ramificationIdx_eq_one (q.map e) T, mul_one]

/-- An algebra equivalence transports the complete prime-indexed conclusion.
Every prime on the target side is pulled back; its lying-over condition, index,
and residue algebra are transported by proved maps. -/
theorem allPrimeData_of_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p : Ideal R) (e : S ≃ₐ[R] T) {n : ℕ}
    (h : ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p],
      P.ramificationIdx R = n ∧ Algebra.IsSeparable (R ⧸ p) (S ⧸ P))
    (Q : Ideal T) [Q.IsPrime] [Q.LiesOver p] :
    Q.ramificationIdx R = n ∧ Algebra.IsSeparable (R ⧸ p) (T ⧸ Q) := by
  let P := Q.comap e.toRingHom
  have : P.IsPrime := Ideal.IsPrime.comap e.toRingHom
  have : P.LiesOver p := by
    constructor
    change p = Ideal.comap (algebraMap R S) (Q.comap e.toRingHom)
    have he : e.toRingHom.comp (algebraMap R S) = algebraMap R T := by
      ext r
      exact e.commutes r
    rw [Ideal.comap_comap, he]
    exact Q.over_def p
  obtain ⟨hidx, hsep⟩ := h P
  have hmap : P.map e = Q := Ideal.map_comap_of_surjective e e.surjective Q
  refine ⟨?_, ?_⟩
  · rw [← hmap, ramificationIdx_map_algEquiv e P, hidx]
  · let σ : (S ⧸ P) ≃ₐ[R] T ⧸ Q := Ideal.quotientEquivAlg P Q e hmap.symm
    let τ : (S ⧸ P) ≃ₐ[R ⧸ p] T ⧸ Q :=
      σ.extendScalarsOfSurjective (R := R) (S := R ⧸ p) Ideal.Quotient.mk_surjective
    exact (AlgEquiv.Algebra.isSeparable_iff τ).mp hsep

/-- Localizing the target at its specified prime preserves the actual index.
This follows from the tower formula and the proved unramifiedness of localization. -/
theorem ramificationIdx_localization_atPrime
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).ramificationIdx R = Q.ramificationIdx R := by
  let A := Localization.AtPrime Q
  have : (IsLocalRing.maximalIdeal A).LiesOver Q :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal A Q).symm⟩
  have : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := A) Q.primeCompl
  have : Algebra.FormallyUnramified A (Localization.AtPrime (IsLocalRing.maximalIdeal A)) :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := Localization.AtPrime (IsLocalRing.maximalIdeal A))
      (IsLocalRing.maximalIdeal A).primeCompl
  have : Algebra.IsUnramifiedAt S (IsLocalRing.maximalIdeal A) :=
    Algebra.FormallyUnramified.comp S A _
  rw [Ideal.ramificationIdx_tower (q := Q),
    Ideal.ramificationIdx_eq_one (IsLocalRing.maximalIdeal A) S, mul_one]

/-- A maximal ideal and its localization have the same residue algebra,
with the specified original scalar ring retained. -/
noncomputable def quotient_equiv_local_residue
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsMaximal] :
    (S ⧸ Q) ≃ₐ[R] Localization.AtPrime Q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
  (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Localization.AtPrime Q)).restrictScalars R

end ZInQ.Contrib.Abhyankar
