import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.FrobeniusTrace

/-!
# Theorem 5.3, Lane RC32 round 4: narrowing the GLUE `FrobeniusTrace`

The leaf `CommonCoordinateInputsLF` (`CommonCoordinate6.lean`) carries the GLUE
`TateWiring.FrobeniusTrace E` as a conjunct: for every good odd prime `r` and every arithmetic
Frobenius element `h ∈ G_ℚ` at `r`, `tr (ρ_T(h) | T₂(E/ℚ̄)) = a_r`. The RC53 group's
`CloudB3RC53/ModularWeil/FrobeniusTrace.lean` derives the **local** dictionary
`GoodReductionFrobeniusTraceDictionaryQ` from two classical inputs, (R) `TateReductionComparison`
and (D) `DetEqDegree` (`goodReductionFrobeniusTraceDictionaryQ_of_RD`).

**What differs.** The two statements agree on the Frobenius convention (arithmetic, `x ↦ x^r` on
residues), on the coefficient (`r + 1 − #Ẽ(𝔽_r)`, which is Mathlib's `E.LFunction r` at good
reduction, `lFunction_prime_eq_card_ZMod`) and include `ℓ = 2` (the dictionary is for every
`ℓ ≠ r`). They differ in substance in two places:

* **global vs local**: `FrobeniusTrace` is about `h ∈ G_ℚ = Aut(ℚ̄/ℚ)` acting on `T₂(E/ℚ̄)`, the
  dictionary about `σ ∈ Gal(ℚ̄_r/ℚ_r)` (an arithmetic Frobenius for a valuation `w` of `ℚ̄_r`
  extending `v_r`) acting on `T₂(E/ℚ̄_r)`. Passing between them is the classical
  decomposition-group comparison: `h` extends to such a `σ` along an embedding `ℚ̄ → ℚ̄_r` centred
  at the prime of `h`, and the embedding identifies the Tate modules equivariantly. It is stated
  here as the named input `LocalGlobalFrobenius E`, the only remaining difference;
* **good reduction**: `FrobeniusTrace` reads it as lane RC13's `Nonvanishing.GoodAt` (integral
  coefficients, unit discriminant), the dictionary as good reduction of the chosen minimal model
  (`GoodReductionAt`). The implication is PROVED here (`goodReductionAt_of_goodAt`).

Results (PROVED from the named inputs; standard axioms):

* `goodReductionAt_of_goodAt`;
* `frobeniusTrace_of_dictionary : GoodReductionFrobeniusTraceDictionaryQ → LocalGlobalFrobenius E →
  FrobeniusTrace E` (the trace is conjugation-invariant, and the dictionary gives it in a basis of
  the local Tate module);
* `frobeniusTrace_of_RD : TateReductionComparison → DetEqDegree → LocalGlobalFrobenius E →
  FrobeniusTrace E`.

Kinds: definitions, PROVED; the inputs (R), (D) (stated by the RC53 group, Silverman AEC VII.3.1,
VII.7.1, III.8.6) and `LocalGlobalFrobenius` (GLUE: Neukirch, ANT II.8–9 and II.4, the
decomposition group and the completion; Silverman AEC VII.4–7 for the Tate modules) are hypotheses.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar TateMod tateRep)
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (GoodReductionFrobeniusTraceDictionaryQ
  GoodReductionAt primeIdealQ IsArithmeticFrobeniusOnClosureQ localTateMatrixQ
  lFunction_prime_eq_card_ZMod goodReductionAt_of_valuation_data nonempty_localTateBasisQ)
open ZInQ.Contrib.CloudB3RC53.ModularWeil (TateReductionComparison DetEqDegree
  goodReductionFrobeniusTraceDictionaryQ_of_RD)
open scoped WithZero

/-! ## Good reduction: `Nonvanishing.GoodAt` gives `GoodReductionAt` -/

/-- A natural number lies in the prime `(p)` of `𝓞 ℚ` exactly when `p` divides it (PROVED). -/
theorem natCast_mem_primeIdealQ_iff {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ (primeIdealQ p hp).asIdeal ↔ p ∣ n := by
  change (n : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  constructor
  · intro h
    have h' := map_dvd Rat.ringOfIntegersEquiv h
    rw [map_natCast, map_natCast] at h'
    exact Int.natCast_dvd_natCast.mp h'
  · intro h
    exact map_dvd (Nat.castRingHom (𝓞 ℚ)) h

/-- An integer lies in the prime `(p)` of `𝓞 ℚ` exactly when `p` divides it (PROVED). -/
theorem intCast_mem_primeIdealQ_iff {p : ℕ} (hp : p.Prime) (n : ℤ) :
    (n : 𝓞 ℚ) ∈ (primeIdealQ p hp).asIdeal ↔ (p : ℤ) ∣ n := by
  change (n : 𝓞 ℚ) ∈ Ideal.span {(p : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  constructor
  · intro h
    have h' := map_dvd Rat.ringOfIntegersEquiv h
    rwa [map_natCast, map_intCast] at h'
  · intro h
    have h' := map_dvd (Int.castRingHom (𝓞 ℚ)) h
    rwa [map_natCast, eq_intCast] at h'

/-- `p`-integrality of a rational number (PROVED). -/
theorem valuation_le_one_of_not_dvd_den {p : ℕ} (hp : p.Prime) {x : ℚ} (h : ¬ p ∣ x.den) :
    (primeIdealQ p hp).valuation ℚ x ≤ 1 :=
  Rat.valuation_le_one_iff_den.mpr fun hmem => h ((natCast_mem_primeIdealQ_iff hp _).mp hmem)

/-- A nonzero rational number of `p`-adic valuation zero is a `p`-adic unit (PROVED). -/
theorem valuation_eq_one_of_padicValRat {p : ℕ} (hp : p.Prime) {x : ℚ} (hx : x ≠ 0)
    (h : padicValRat p x = 0) : (primeIdealQ p hp).valuation ℚ x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hnum0 : x.num ≠ 0 := Rat.num_ne_zero.mpr hx
  have hcop : Nat.Coprime x.num.natAbs x.den := x.reduced
  have hnum : ¬ (p : ℤ) ∣ x.num := by
    intro hd
    have hden : ¬ p ∣ x.den := by
      intro hd'
      have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp hd
      have h3 : p ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd h1 hd'
      rw [hcop.gcd_eq_one] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    have hv : padicValRat p x = padicValInt p x.num - padicValNat p x.den := rfl
    rw [hv, padicValNat.eq_zero_of_not_dvd hden, Nat.cast_zero, sub_zero] at h
    have h2 : 1 ≤ padicValInt p x.num := by
      rw [padicValInt]
      exact one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum0) (Int.natCast_dvd.mp hd)
    omega
  have hden : ¬ p ∣ x.den := by
    intro hd'
    have hv : padicValRat p x = padicValInt p x.num - padicValNat p x.den := rfl
    rw [hv, padicValInt.eq_zero_of_not_dvd hnum, Nat.cast_zero, zero_sub, neg_eq_zero] at h
    have h2 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero hd'
    omega
  have hn : (primeIdealQ p hp).valuation ℚ (x.num : ℚ) = 1 := by
    simpa only [map_intCast] using
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := primeIdealQ p hp)
        (r := (x.num : 𝓞 ℚ))).mpr fun hm => hnum ((intCast_mem_primeIdealQ_iff hp _).mp hm)
  have hd : (primeIdealQ p hp).valuation ℚ (x.den : ℚ) = 1 := by
    simpa only [map_natCast] using
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := primeIdealQ p hp)
        (r := (x.den : 𝓞 ℚ))).mpr fun hm => hden ((natCast_mem_primeIdealQ_iff hp _).mp hm)
  rw [← x.num_div_den, map_div₀, hn, hd, div_one]

/-- **Good reduction in `FrobeniusTrace`'s sense gives good reduction in the dictionary's**
(PROVED): `p`-integral coefficients and a `p`-adic unit discriminant make the base change to `ℚ_p`
integral with unit discriminant, so its minimal model has good reduction (the RC53 group's
`goodReductionAt_of_valuation_data`). -/
theorem goodReductionAt_of_goodAt {E : WeierstrassCurve ℚ} {p : ℕ} (hp : p.Prime)
    (h : Nonvanishing.GoodAt E p) : GoodReductionAt E (primeIdealQ p hp) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆, hΔ0, hΔ⟩ := h
  exact goodReductionAt_of_valuation_data E _ (valuation_le_one_of_not_dvd_den hp h₁)
    (valuation_le_one_of_not_dvd_den hp h₂) (valuation_le_one_of_not_dvd_den hp h₃)
    (valuation_le_one_of_not_dvd_den hp h₄) (valuation_le_one_of_not_dvd_den hp h₆)
    (valuation_eq_one_of_padicValRat hp hΔ0 hΔ)

/-! ## The local-global comparison and the bridge -/

section Bridge

open scoped Classical

variable (E : WeierstrassCurve ℚ)

/-- The `2`-adic Tate module of `E` over an algebraic closure of `ℚ_r` (the dictionary's local
Tate module at `ℓ = 2`). -/
abbrev localTate (r : ℕ) (hr : r.Prime) : Type :=
  TauCeti.TateModule 2 ((E.baseChange ((primeIdealQ r hr).adicCompletion ℚ)).baseChange
    (AlgebraicClosure ((primeIdealQ r hr).adicCompletion ℚ))).toAffine.Point

/-- **The local-global comparison at the good odd primes** (GLUE: the decomposition group and the
completion, Neukirch ANT II.8–9; the Tate module over `ℚ̄_r`, Silverman AEC VII.4–7). For an
arithmetic Frobenius element `h ∈ G_ℚ` at a good odd prime `r` there are a valuation `w` of `ℚ̄_r`
extending `v_r`, an arithmetic Frobenius `σ ∈ Gal(ℚ̄_r/ℚ_r)` for `w` (the extension of `h` along an
embedding `ℚ̄ → ℚ̄_r` centred at the prime of `h`), and a `ℤ₂`-linear isomorphism
`T₂(E/ℚ̄) ≃ T₂(E/ℚ̄_r)` carrying `ρ_T(h)` to the action of `σ`. -/
def LocalGlobalFrobenius : Prop :=
  ∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → Nonvanishing.GoodAt E r → ∀ h : GalQ,
    ZInQ.Contrib.ChebFD.C10.IsFrobAt h r →
      ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
        (w : Valuation (AlgebraicClosure ((primeIdealQ r hr).adicCompletion ℚ)) Γ),
        (w.comap (algebraMap ((primeIdealQ r hr).adicCompletion ℚ)
          (AlgebraicClosure ((primeIdealQ r hr).adicCompletion ℚ)))).IsEquiv
          (Valued.v : Valuation ((primeIdealQ r hr).adicCompletion ℚ) ℤᵐ⁰) ∧
        ∃ σ : AlgebraicClosure ((primeIdealQ r hr).adicCompletion ℚ) ≃ₐ[
            (primeIdealQ r hr).adicCompletion ℚ]
              AlgebraicClosure ((primeIdealQ r hr).adicCompletion ℚ),
          IsArithmeticFrobeniusOnClosureQ (primeIdealQ r hr) Γ w σ ∧
          ∃ e : TateMod E 2 ≃ₗ[ℤ_[2]] localTate E r hr,
            ∀ x, e (tateRep E 2 h x) =
              (E.baseChange ((primeIdealQ r hr).adicCompletion ℚ)).tateModuleGaloisRepresentation
                2 σ (e x)

/-- **`FrobeniusTrace` from the local dictionary and the local-global comparison** (PROVED): the
trace of `ρ_T(h)` on `T₂(E/ℚ̄)` is the trace of the local Frobenius `σ` on `T₂(E/ℚ̄_r)` (conjugation
by the comparison), which the dictionary computes in a basis as `r + 1 − #Ẽ(𝔽_r) = a_r`. -/
theorem frobeniusTrace_of_dictionary (hD : GoodReductionFrobeniusTraceDictionaryQ)
    [hE : E.IsElliptic] (hLG : LocalGlobalFrobenius E) : FrobeniusTrace E := by
  intro r hr hr2 hgood h hF
  obtain ⟨Γ, inst, w, hw, σ, hσ, e, he⟩ := hLG r hr hr2 hgood h hF
  have hgoodR := goodReductionAt_of_goodAt hr hgood
  obtain ⟨b⟩ := nonempty_localTateBasisQ E hE (primeIdealQ r hr) 2
  have h2r : (2 : ℕ) ≠ r := fun h' => hr2 h'.symm
  obtain ⟨htr, -⟩ := hD E hE r hr hgoodR 2 h2r Γ w hw σ hσ b
  rw [localTateMatrixQ, ← LinearMap.trace_eq_matrix_trace] at htr
  have hQ2 : ((2 : ℕ) : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr two_ne_zero
  have := (E.baseChange Qbar).free_tateModule hQ2
  have := (E.baseChange Qbar).finite_tateModule hQ2
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  set ρσ := (E.baseChange ((primeIdealQ r hr).adicCompletion ℚ)).tateModuleGaloisRepresentation
    (K := AlgebraicClosure ((primeIdealQ r hr).adicCompletion ℚ)) 2 σ with hρσ
  have hconj : tateRep E 2 h = e.symm.conj ρσ := by
    refine LinearMap.ext fun x => ?_
    apply e.injective
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, he]
  rw [hconj, LinearMap.trace_conj', htr, lFunction_prime_eq_card_ZMod E r hr hgoodR]
  push_cast
  ring

/-- **`FrobeniusTrace` from (R), (D) and the local-global comparison** (PROVED): the RC53
group's `goodReductionFrobeniusTraceDictionaryQ_of_RD` and `frobeniusTrace_of_dictionary`. -/
theorem frobeniusTrace_of_RD (hR : TateReductionComparison) (hD : DetEqDegree) [E.IsElliptic]
    (hLG : LocalGlobalFrobenius E) : FrobeniusTrace E :=
  frobeniusTrace_of_dictionary E (goodReductionFrobeniusTraceDictionaryQ_of_RD hR hD) hLG

end Bridge

end ZInQ.Manuscript.RC.Wiring
