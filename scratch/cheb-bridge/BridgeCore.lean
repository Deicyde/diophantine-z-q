import Mathlib

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.ChebBridge

variable (M : Type) [Field M] [NumberField M]

/-- `ℤ → 𝓞 ℚ` is surjective, hence `𝓞 ℚ`-unramifiedness implies `ℤ`-unramifiedness. -/
theorem isUnramifiedAt_int_of_ratInt (Q : Ideal (𝓞 M)) [Q.IsPrime]
    (h : Algebra.IsUnramifiedAt (𝓞 ℚ) Q) : Algebra.IsUnramifiedAt ℤ Q := by
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
      (Rat.int_algebraMap_surjective (𝓞 ℚ))
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime Q)

theorem card_quot_int (I : Ideal (𝓞 ℚ)) :
    Nat.card (ℤ ⧸ I.comap (algebraMap ℤ (𝓞 ℚ))) = Nat.card (𝓞 ℚ ⧸ I) := by
  let e : ℤ ≃+* 𝓞 ℚ := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm
  have he : (e : ℤ →+* 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) := Subsingleton.elim _ _
  refine Nat.card_congr (Ideal.quotientEquiv _ _ e ?_).toEquiv
  rw [he]
  exact (Ideal.map_comap_of_surjective _ (Rat.int_algebraMap_surjective (𝓞 ℚ)) I).symm

/-- The Frobenius congruence over `𝓞 ℚ`, unfolded (so that no `SMulCommClass Gal(M/ℚ) (𝓞 ℚ) (𝓞 M)`
instance is needed to state it), gives `IsArithFrobAt ℤ`. -/
theorem isArithFrobAt_int (Q : Ideal (𝓞 M)) (σ : M ≃ₐ[ℚ] M)
    (h : ∀ x : 𝓞 M, σ • x - x ^ Nat.card (𝓞 ℚ ⧸ Q.under (𝓞 ℚ)) ∈ Q) :
    IsArithFrobAt ℤ σ Q := by
  intro x
  have hx := h x
  have hQ : Q.under ℤ = (Q.under (𝓞 ℚ)).comap (algebraMap ℤ (𝓞 ℚ)) :=
    (Ideal.under_under Q).symm
  rw [hQ, card_quot_int]
  exact hx

theorem under_int_eq (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 M))
    [Q.LiesOver 𝔭.asIdeal] :
    Q.under ℤ = Ideal.span {((Rat.HeightOneSpectrum.natGenerator 𝔭 : ℕ) : ℤ)} := by
  rw [Rat.HeightOneSpectrum.span_natGenerator, ← Ideal.under_under (B := 𝓞 ℚ),
    ← Ideal.LiesOver.over (P := Q) (p := 𝔭.asIdeal), ← Ideal.comap_symm]
  ext x
  simp only [Ideal.under, Ideal.mem_comap, eq_intCast]

theorem natGenerator_injective :
    Function.Injective (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)) :=
  fun _ _ h => Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

/-- The bridge: an infinite set of unramified primes of `𝓞 ℚ` at each of which `σ` is a
Frobenius at some prime above gives the existence form of Chebotarev. -/
theorem exists_of_infinite (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (hT : T.Infinite)
    (hur : ∀ 𝔭 ∈ T, ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 ℚ) Q)
    (hfrob : ∀ 𝔭 ∈ T, ∃ Q : 𝔭.asIdeal.primesOver (𝓞 M),
      ∀ x : 𝓞 M, σ • x - x ^ Nat.card (𝓞 ℚ ⧸ Q.1.under (𝓞 ℚ)) ∈ Q.1) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q := by
  have hfin : (Rat.HeightOneSpectrum.natGenerator ⁻¹' (S : Set ℕ) :
      Set (HeightOneSpectrum (𝓞 ℚ))).Finite :=
    S.finite_toSet.preimage natGenerator_injective.injOn
  obtain ⟨𝔭, h𝔭T, h𝔭S⟩ := (hT.sdiff hfin).nonempty
  obtain ⟨⟨Q, hQm⟩, hQ⟩ := hfrob 𝔭 h𝔭T
  have : Q.IsPrime := hQm.1
  have : Q.LiesOver 𝔭.asIdeal := hQm.2
  exact ⟨_, Rat.HeightOneSpectrum.prime_natGenerator 𝔭, h𝔭S, Q, inferInstance,
    under_int_eq M 𝔭 Q, isUnramifiedAt_int_of_ratInt M Q (hur 𝔭 h𝔭T Q),
    isArithFrobAt_int M Q σ hQ⟩

end ZInQ.Contrib.ChebBridge
