/-
The theorems `ZInQ.Contrib.chebotarevExists` and `ZInQ.Contrib.chebotarevExists_c10` below rest on
Tau Ceti's Chebotarev density theorem (https://github.com/TauCetiProject/TauCeti, Apache-2.0,
"The Tau Ceti contributors"), vendored under `ZInQKernel/Contrib/TauCeti/` by task tc-port.
-/
import ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.C10.C10

/-!
# Leaf I6.4 / T18 (Chebotarev, existence form), proved

`PkgI6.ChebotarevExists` (`ZInQKernel/HDecomp/Conductor/I6Base.lean`) and its verbatim copy
`GlueC10.ChebotarevExists` (`ZInQKernel/HDecomp/C10/C10.lean`) say: for a finite Galois
extension `M/ℚ`, an element `σ ∈ Gal(M/ℚ)` and a finite set `S` of naturals, there is a prime
`p ∉ S` and a prime `Q` of `𝓞 M` over `p`, unramified over `ℤ`, at which `σ` is an arithmetic
Frobenius (`IsArithFrobAt ℤ σ Q`).

Proof.  Tau Ceti's `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` gives the set of
primes `𝔭` of `𝓞 ℚ` unramified in `M` with Artin class `[σ]` the natural density
`#[σ] / #Gal(M/ℚ) ≠ 0`, so the set is infinite (`NumberField.Set.HasNaturalDensity.infinite`).
Remove the finitely many `𝔭` whose generator lies in `S` (`𝔭 ↦ p` is Mathlib's injective
`Rat.HeightOneSpectrum.natGenerator`).  For a remaining `𝔭`,
`exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk` gives a prime `Q` over `𝔭` with
`IsArithFrobAt (𝓞 ℚ) σ Q` (σ itself, not a conjugate), and `isUnramifiedAt_of_mem_frobeniusPrimeSet`
gives `Algebra.IsUnramifiedAt (𝓞 ℚ) Q`.  The passage from the base `𝓞 ℚ` to the base `ℤ` uses that
`ℤ → 𝓞 ℚ` is bijective: `#(ℤ ⧸ Q ∩ ℤ) = #(𝓞 ℚ ⧸ 𝔭)`, `Q ∩ ℤ = (p)`, and formal unramifiedness
composes along the surjection `ℤ → 𝓞 ℚ`.

## Main results

* `ZInQ.Contrib.chebotarevExists : PkgI6.ChebotarevExists`
* `ZInQ.Contrib.chebotarevExists_c10 : GlueC10.ChebotarevExists`

No `sorry`, no `axiom`.
-/

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

namespace ZInQ.Contrib

open NumberField.Chebotarev in
/-- **Leaf I6.4 (Chebotarev, existence form), proved** from Tau Ceti's Chebotarev density
theorem. -/
theorem chebotarevExists : PkgI6.ChebotarevExists := by
  intro M _ _ _ S σ
  have hd := hasNaturalDensity_frobeniusPrimeSet ℚ M (ConjClasses.mk σ)
  have hinf := hd.infinite ((ConjClasses.mk σ).card_carrier_div_card_ne_zero
    (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
  refine ChebBridge.exists_of_infinite M S σ _ hinf ?_ ?_
  · intro 𝔭 h𝔭 Q _ _
    exact isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q
  · intro 𝔭 h𝔭
    obtain ⟨Q, hQ⟩ := exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
    exact ⟨Q, fun x => hQ x⟩

/-- **Leaf I6.4 in its `GlueC10` copy (verbatim the same statement), proved.** -/
theorem chebotarevExists_c10 : GlueC10.ChebotarevExists := chebotarevExists

end ZInQ.Contrib
