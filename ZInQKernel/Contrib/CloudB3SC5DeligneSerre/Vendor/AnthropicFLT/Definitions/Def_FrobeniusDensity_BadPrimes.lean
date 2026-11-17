/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_FrobeniusDensity_BadPrimes (git blob 63887194c516d68e73c34891eb6b32a2f9c18b56, sha256 5c757222b2715ab2b31b337d7a07d29ff5fe349a41e3138d2d5c99f515415f96).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.ZMod.QuotientRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace FrobeniusDensity

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

theorem card_quotient_ratPrimeIdeal (ℓ : ℕ) :
    Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [ratPrimeIdeal, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

theorem card_quotient_under_int {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
  rw [← Q.over_def (ratPrimeIdeal ℓ), card_quotient_ratPrimeIdeal]

section Ramified

variable {K : Type*} [Field K] [NumberField K]

lemma finite_setOf_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}.Finite := by
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      {v | v.asIdeal ∣ I} := fun v _ w _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (normalizedFactors I).toFinset.finite_toSet.subset ?_
  rintro J ⟨v, hv, rfl⟩
  exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr -- [port]
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩))

variable (L : Type*) [Field L] [NumberField L]

theorem exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) :
    ∃ x : 𝓞 L, g • x ≠ x := by
  by_contra hcon'
  have hcon : ∀ x : 𝓞 L, g • x = x := fun x => not_not.mp fun h => hcon' ⟨x, h⟩
  refine hg (AlgEquiv.ext fun z => ?_)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) z
  have hx : g (algebraMap (𝓞 L) L x) = algebraMap (𝓞 L) L x :=
    congrArg (algebraMap (𝓞 L) L) (hcon x)
  have hy' : g (algebraMap (𝓞 L) L y) = algebraMap (𝓞 L) L y :=
    congrArg (algebraMap (𝓞 L) L) (hcon y)
  rw [← hxy, map_div₀, hx, hy', AlgEquiv.one_apply]

theorem finite_setOf_inertia_ne_bot_heightOneSpectrum :
    {v : HeightOneSpectrum (𝓞 L) | v.asIdeal.inertia (L ≃ₐ[ℚ] L) ≠ ⊥}.Finite := by
  classical
  choose x hx using fun g : {g : L ≃ₐ[ℚ] L // g ≠ 1} => exists_smul_ne L g.2
  refine Set.Finite.subset (Set.Finite.biUnion
    (Set.finite_univ (α := {g : L ≃ₐ[ℚ] L // g ≠ 1}))
    (fun g _ => finite_setOf_dvd (I := Ideal.span {g.1 • x g - x g}) ?_)) ?_
  · rw [Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    exact hx g
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    obtain ⟨g, hgmem, hgne⟩ := (v.asIdeal.inertia (L ≃ₐ[ℚ] L)).bot_or_exists_ne_one.resolve_left hv
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨⟨g, hgne⟩, Set.mem_univ _, ?_⟩
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hgmem (x ⟨g, hgne⟩)

noncomputable def badPrimes : Finset ℕ :=
  insert 0 (insert 1 (((finite_setOf_inertia_ne_bot_heightOneSpectrum L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

theorem inertia_eq_bot_of_notMem_badPrimes {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓbad : ℓ ∉ badPrimes L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] :
    Q.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  by_contra hcon
  apply hℓbad
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver_ratPrimeIdeal hℓ
  refine Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ?_)))
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨Q, inferInstance, hQbot⟩, hcon, card_quotient_under_int (ℓ := ℓ) Q⟩

end Ramified

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem degOneCount_of_not_prime {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) : degOneCount K ℓ = 0 := by
  rw [degOneCount, if_neg hℓ]

omit [NumberField K] in
theorem degOneCount_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    degOneCount K ℓ
      = {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard := by
  rw [degOneCount, if_pos hℓ]

end DegOneCount

section Frob

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

theorem isConj_arithFrobAt_of_liesOver {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₁ Q₂ : Ideal (𝓞 L))
    [Q₁.IsPrime] [Q₂.IsPrime] [Q₁.LiesOver (ratPrimeIdeal ℓ)] [Q₂.LiesOver (ratPrimeIdeal ℓ)] :
    letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    IsConj (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₂) := by
  letI : Finite (𝓞 L ⧸ Q₁) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  letI : Finite (𝓞 L ⧸ Q₂) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  exact isConj_arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₁ Q₂
    ((Q₁.over_def (ratPrimeIdeal ℓ)).symm.trans (Q₂.over_def (ratPrimeIdeal ℓ)))

variable (L)

theorem realizesCyclicAt_of_exists (σ : L ≃ₐ[ℚ] L) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime] [Q₀.LiesOver (ratPrimeIdeal ℓ)]
    (h : ∀ _ : Finite (𝓞 L ⧸ Q₀),
      ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀)) :
    RealizesCyclicAt L σ ℓ := by
  refine ⟨hℓ, fun Q hQp hQl hQf => ?_⟩
  haveI : Finite (𝓞 L ⧸ Q₀) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := h ‹_›
  exact ⟨k, hk, hconj.trans (isConj_arithFrobAt_of_liesOver hℓ Q₀ Q)⟩

end Frob

end FrobeniusDensity
