# G0 representation route: invariants versus coinvariants

## The multiplicative-reduction obstruction

Let `p ≠ ℓ`, and let an elliptic curve have multiplicative reduction at `p`.
Write `ε` for the unramified quadratic character, trivial in the split case.
The homological rational Tate representation `V = ℚ_ℓ ⊗ T_ℓ(E)` has Tate-curve
shape

`0 → ℚ_ℓ(1) ⊗ ε → V → ℚ_ℓ ⊗ ε → 0`.

Its nontrivial unipotent inertia action gives

* `V^I = ℚ_ℓ(1) ⊗ ε`, with arithmetic Frobenius eigenvalue `ε(p) p`;
* `V_I = V / ⟨ρ(i)v − v⟩ = ℚ_ℓ ⊗ ε`, with arithmetic Frobenius eigenvalue `ε(p)`.

Thus the reversed characteristic polynomial on the invariants is
`1 − ε(p) p X`, whereas the classical local Euler polynomial is
`1 − ε(p) X`. In short, **1 − εpX is not 1 − εX**. The distinction cannot be
removed by a coefficient-field embedding or by choosing another auxiliary prime.

For **11a1 at `p = 11`**, the reduction is split multiplicative, so `ε(p) = 1`.
The invariant polynomial of the homological representation is `1 − 11 X`,
but the classical polynomial is `1 − X`, for every auxiliary prime `ℓ ≠ 11`.
The same obstruction applies to the rational newform of level 11 and its
homological Galois representation.

Consequently the invariant-space local-factor clause of the historical
realization and the two historical Carayol propositions below are not valid
local readings of the classical factors. The historical bad-reduction
proposition is also false. The conditional comparison and assembly theorems
that consumed these interfaces were formally valid implications from their
hypotheses, but those hypotheses made the route unusable. They are archived
rather than retained as active Lean declarations.

References for the normalization: Silverman, *The Arithmetic of Elliptic
Curves*, Appendix C, §14 and §16; Carayol 1986, §§0.4–0.8, pp. 409–411.

## The retained definition and the corrected route

`ZInQKernel/Contrib/RC53Assist/NewformGlueG0/GaloisCompletion.lean` retains
`Completion.localTatePolynomial` as a definition of the invariant polynomial,
with the multiplicative-reduction warning. Its good-reduction reading remains
proved, since inertia is trivial at a good prime `p ≠ ℓ`.

The correct coinvariant readings are in
`ZInQKernel/Contrib/RC53Assist/GlobalTrace/CoinvariantReadings.lean`:

* `coinvariantEulerPolynomial` and `localTatePolynomialCoinv` use arithmetic
  Frobenius on the inertia coinvariants of the homological representation.
* `CarayolRationalRealizationCoinv` retains exactly the other four field types
  (`normalizedRep`, `continuous_matrix`, `irreducible`, `good_trace`) and uses
  the coinvariant polynomial in `local_factor`.
* `Carayol1986ThmARationalWeightTwoCoinv` and
  `BadReductionTatePolynomialReadingCoinv` are the corrected explicit
  propositions. They are theorem parameters, not new axioms or claimed proofs
  of the literature inputs.
* `tate_equiv_of_good_traces` preserves the comparison using only continuity,
  irreducibility and good-prime traces of the normalized representation.
  `localTatePolynomialCoinv_eq_newform_of_comparison` transports the corrected
  local polynomial through the resulting representation isomorphism.
* `CarayolRationalRealizationCoinv.cohomologicalRep` is the dual of
  `normalizedRep`; the definition is the true dual-normalization piece moved
  from the historical realization.
* `coinvariantEulerPolynomial_eq_dual`, `localTatePolynomialCoinv_eq_dual`
  and `CarayolRationalRealizationCoinv.local_factor_cohomological` prove that
  arithmetic Frobenius on these coinvariants gives the same polynomial as
  geometric Frobenius on the inertia invariants of the dual representation.
* The existing additive- and multiplicative-reduction proofs, including
  `coinvariantEulerPolynomial_of_tateShape`, are preserved. They compute the
  classical polynomial from the stated Tate-curve, local–global and
  additive-vanishing inputs.

`GlobalTrace/GoodReductionReading.lean` retains all its rational-model,
place-reduction, inertia, trace and determinant proofs. The corrected assembly
in `GlobalTrace/CoinvariantAssembly.lean` uses
`globalGoodReductionTraceReading_proved` and the corrected local readings.
It remains conditional on the displayed literature and bad-prime inputs.

The printed-corollary route in `NewformGlueG0/GaloisCompletion.lean` is
independent of the removed invariant-space interfaces. Its declarations,
four input propositions and supporting code are unchanged; only explanatory
comments and source labels are revised. The joint Shimura–Carayol factor
reading and the local-factor reading of Faltings are labeled GLUE, not PRINT.

## Historical declarations: text only, not Lean source

The code blocks below preserve the excluded declaration text. Except for the
last theorem, their original namespace was
`ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion`; the last theorem was in
`ZInQ.Contrib.RC53Assist.GlobalTrace`. These blocks are an archival record of
the invariant-space route, not inputs to the corrected route.

### `CarayolRationalRealization`

```lean
structure CarayolRationalRealization {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime] where
  /-- **PRINTED DATA**, the dual-normalized representation. Locator: Carayol (A), pp. 410–411. -/
  normalizedRep : Representation ℚ_[ℓ] GlueC10.GQ (Fin 2 → ℚ_[ℓ])
  /-- **PRINTED PROPERTY**, coordinate continuity. Locator: Carayol (A), pp. 410–411. -/
  continuous_matrix : Continuous fun g : GlueC10.GQ =>
    LinearMap.toMatrix (Pi.basisFun ℚ_[ℓ] (Fin 2)) (Pi.basisFun ℚ_[ℓ] (Fin 2)) (normalizedRep g)
  /-- **PRINTED PROPERTY**, the irreducibility Remarque after (A), p. 411. -/
  irreducible : normalizedRep.IsIrreducible
  /-- **PRINTED GOOD-PRIME READING**, arithmetic trace. Locator: Carayol §§0.5–0.7, pp. 410–411. -/
  good_trace : ∀ (p : ℕ), p.Prime → ¬p ∣ M * ℓ →
    ∀ g : GlueC10.GQ, GlueC10.IsFrobAt g p →
      LinearMap.trace ℚ_[ℓ] (Fin 2 → ℚ_[ℓ]) (normalizedRep g) = (b p : ℚ_[ℓ])
  /-- **CONSEQUENCE OF PRINTED LOCAL COMPATIBILITY**, at every `p ≠ ℓ`,
  with the actual subgroup and actual Frobenius. Locators: Carayol (A), pp. 410–411;
  Li Theorem 3(i), p. 295; Casselman Theorem 4, p. 313.

  **Warning: false as stated at primes of multiplicative reduction.** The polynomial uses the
  arithmetic Frobenius on the inertia invariants of the homological representation. For a Tate
  curve the invariants are the line `ℚ_ℓ(1) ⊗ ε`, on which the arithmetic Frobenius acts by `ε p`,
  so this side is `1 - ε p X`, while the classical factor is `1 - ε X` (for the curve 11a1 at
  `p = 11`: `1 - 11 X` against `1 - X`). The correct reading uses the inertia coinvariants
  (equivalently the dual representation with the inverse Frobenius). The printed-corollary route
  `Descent.liCarayolNewformOfModular_of_printed_corollaries` does not use this statement. -/
  local_factor : ∀ (p : ℕ), p.Prime → p ≠ ℓ → ∀ D : LocalArithmeticFrobenius p,
    inertiaEulerPolynomial normalizedRep (inertiaAt D) D.element (inertiaAt_normalized D) =
      rationalNewformPolynomial M ℓ b p
```

### `CarayolRationalRealization.cohomologicalRep`

```lean
def CarayolRationalRealization.cohomologicalRep {M : ℕ} [NeZero M]
    {F : Newform M 2} {hχ : F.χ = 1} {b : ℕ → ℚ}
    {hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ)}
    {ℓ : ℕ} [Fact ℓ.Prime] (R : CarayolRationalRealization F hχ b hb ℓ) :
    Representation ℚ_[ℓ] GlueC10.GQ (Module.Dual ℚ_[ℓ] (Fin 2 → ℚ_[ℓ])) :=
  R.normalizedRep.dual
```

### `Carayol1986ThmAWeightTwoQ`

```lean
def Carayol1986ThmAWeightTwoQ : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2), F.χ = 1 →
    ∃ (K : IntermediateField ℚ ℂ) (hK : NumberField K),
      letI := hK
      ∃ hcoeff : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n ∈ K,
        ∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (lam : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          (ℓ : NumberField.RingOfIntegers K) ∈ lam.asIdeal →
          ∃ ρ : Representation (lam.adicCompletion K) GlueC10.GQ (Fin 2 → lam.adicCompletion K),
            Continuous (fun g : GlueC10.GQ =>
              LinearMap.toMatrix (Pi.basisFun (lam.adicCompletion K) (Fin 2))
                (Pi.basisFun (lam.adicCompletion K) (Fin 2)) (ρ g)) ∧
            ρ.IsIrreducible ∧
            (∀ (p : ℕ), p.Prime → ¬p ∣ M * ℓ →
              ∀ g : GlueC10.GQ, GlueC10.IsFrobAt g p →
                LinearMap.trace (lam.adicCompletion K) (Fin 2 → lam.adicCompletion K) (ρ g) =
                  algebraMap K (lam.adicCompletion K)
                    ⟨(qExpansion 1 F.toCuspForm).coeff p, hcoeff p⟩) ∧
            ∀ (p : ℕ), p.Prime → p ≠ ℓ → ∀ D : LocalArithmeticFrobenius p,
              inertiaEulerPolynomial ρ (inertiaAt D) D.element (inertiaAt_normalized D) =
                1 - Polynomial.C (algebraMap K (lam.adicCompletion K)
                    ⟨(qExpansion 1 F.toCuspForm).coeff p, hcoeff p⟩) *
                    (Polynomial.X : Polynomial (lam.adicCompletion K)) +
                  Polynomial.C (if Nat.Coprime p M then (p : lam.adicCompletion K) else 0) *
                    (Polynomial.X : Polynomial (lam.adicCompletion K)) ^ 2
```

### `Carayol1986ThmARationalWeightTwo`

```lean
def Carayol1986ThmARationalWeightTwo : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime], Nonempty (CarayolRationalRealization F hχ b hb ℓ)
```

### `BadReductionTatePolynomialReading`

```lean
def BadReductionTatePolynomialReading : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime), p ≠ ℓ → ¬GoodReductionAt E (primeIdealQ p hp) →
      ∀ D : LocalArithmeticFrobenius p,
        localTatePolynomial E ℓ D =
          (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ])
```

### `tate_equiv_Carayol_of_almost_all_primes`

```lean
theorem tate_equiv_Carayol_of_almost_all_primes
    (hFa : Faltings1983Satz3EllipticQ) (hG : GlobalGoodReductionTraceReading)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (S : Finset ℕ) (hFp : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime] (R : CarayolRationalRealization F hχ b hb ℓ) :
    Nonempty (Representation.Equiv (rationalTateRep E ℓ) R.normalizedRep) := by
  classical
  have hEr : IsSemisimpleModule (MonoidAlgebra ℚ_[ℓ] GlueC10.GQ)
      (rationalTateRep E ℓ).asModule := hFa E ℓ
  have hR : R.normalizedRep.IsIrreducible := R.irreducible
  have hRs : IsSemisimpleModule (MonoidAlgebra ℚ_[ℓ] GlueC10.GQ) R.normalizedRep.asModule :=
    inferInstance
  obtain ⟨T, hT⟩ := goodReductionAt_almost_all_primes E inferInstance
  apply representationEquiv_of_BN_frobenius brauerNesbittChar0 ℚ_[ℓ]
    (rationalTate E ℓ) (Fin 2 → ℚ_[ℓ]) (Fin 2) (Fin 2)
    (rationalTateBasis E ℓ) (Pi.basisFun ℚ_[ℓ] (Fin 2))
    (rationalTateRep E ℓ) R.normalizedRep (continuous_rationalTateRep_matrix E ℓ)
    R.continuous_matrix hEr hRs ((S ∪ T) ∪ (M * ℓ).primeFactors)
  intro g p hp hpNot hg
  have hpS : p ∉ S := fun h => hpNot (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hpT : p ∉ T := fun h => hpNot (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hpMℓ : ¬p ∣ M * ℓ := fun h => hpNot
    (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr
      ⟨hp, h, mul_ne_zero (NeZero.ne M) (Fact.out : ℓ.Prime).ne_zero⟩))
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    exact hpMℓ (dvd_mul_left _ _)
  have hgE := (hG goodReductionFrobeniusTraceDictionaryQ_proved E ℓ p hp hpℓ
    (hT p hp hpT)).2 g hg
  rw [hgE.1, R.good_trace p hp hpMℓ g hg]
  have hbp : b p = (E.LFunction p : ℚ) := by
    have h := (hb p).symm.trans (hFp p hp hpS)
    exact_mod_cast h
  rw [hbp, Rat.cast_intCast]
```

### `localTatePolynomial_eq_newform_of_comparison`

```lean
theorem localTatePolynomial_eq_newform_of_comparison
    (hFa : Faltings1983Satz3EllipticQ) (hG : GlobalGoodReductionTraceReading)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (S : Finset ℕ) (hFp : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime] (R : CarayolRationalRealization F hχ b hb ℓ)
    (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (D : LocalArithmeticFrobenius p) :
    localTatePolynomial E ℓ D = rationalNewformPolynomial M ℓ b p := by
  obtain ⟨e⟩ := tate_equiv_Carayol_of_almost_all_primes hFa hG E F hχ b hb S hFp ℓ R
  exact (inertiaEulerPolynomial_eq_of_equiv e (inertiaAt D) D.element
    (inertiaAt_normalized D)).trans (R.local_factor p hp hpℓ D)
```

### `liCarayolNewformOfModular_of_representations`

```lean
theorem liCarayolNewformOfModular_of_representations
    (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
    (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986ThmARationalWeightTwo) (hFa : Faltings1983Satz3EllipticQ)
    (hG : GlobalGoodReductionTraceReading) (hB : BadReductionTatePolynomialReading) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular := by
  classical
  intro E hE N hN f hf
  have : E.IsElliptic := hE
  obtain ⟨M, hM0, F, hMN, hχ, S, hFp⟩ :=
    exists_newform_almost_all_prime_coeff E hE N hN f hf
  have hrat := ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficients_rational_of_almost_all_primes
    hS hL E F hχ S hFp
  choose b hb using hrat
  have hP : ∀ (p : ℕ) (hp : p.Prime),
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℂ) =
        newformEulerPolynomial F hχ p := by
    intro p hp
    obtain ⟨ℓ, hℓ, hpℓ⟩ := exists_auxiliary_prime_ne p
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨R⟩ := hC M F hχ b hb ℓ
    obtain ⟨D⟩ := localArithmeticFrobenius_nonempty p hp
    have hcompare := localTatePolynomial_eq_newform_of_comparison
      hFa hG E F hχ b hb S hFp ℓ R p hp hpℓ D
    have hT : localTatePolynomial E ℓ D =
        (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) := by
      by_cases hgood : GoodReductionAt E (primeIdealQ p hp)
      · exact localTatePolynomial_of_good hG E ℓ p hp hpℓ hgood D
      · exact hB E ℓ p hp hpℓ hgood D
    exact complexPolynomial_of_adicPolynomial E F hχ b hb ℓ p hp (hT.symm.trans hcompare)
  have hpow := fun p hp r => newform_prime_pow_coeff_of_local_polynomial E F hχ p hp (hP p hp) r
  have hall : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (E.LFunction n : ℂ) := by
    intro n
    induction n using Nat.recOnPrimeCoprime with
    | zero =>
      rw [CuspFormClass.qExpansion_coeff_zero F.toCuspForm one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map M)]
      simp
    | prime_pow p r hp => exact hpow p hp r
    | coprime m n _ _ hmn hm hn =>
      change newformCoefficients F (m * n) = _
      rw [(newformCoefficients_isMultiplicative F).2 hmn,
        newformCoefficients_apply, newformCoefficients_apply, hm, hn,
        (lFunction_isMultiplicative E).2 hmn, Int.cast_mul]
  exact ⟨M, hM0, F, hMN, hχ, fun n _ => hall n⟩
```

### `liCarayolNewformOfModular_of_representations_good_proved`

```lean
theorem liCarayolNewformOfModular_of_representations_good_proved
    (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
    (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986ThmARationalWeightTwo) (hFa : Faltings1983Satz3EllipticQ)
    (hB : BadReductionTatePolynomialReading) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular :=
  liCarayolNewformOfModular_of_representations hS hL hC hFa
    globalGoodReductionTraceReading_proved hB
```

