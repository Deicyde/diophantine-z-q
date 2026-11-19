import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.GaloisCompletion

/-!
# Inertia coinvariants and the corrected local readings of G0

The retained definition `Completion.localTatePolynomial` reads the arithmetic Frobenius on the
inertia *invariants* of the homological (dual-normalized) representation. At primes of
multiplicative reduction this is not the classical factor: the invariants are the line
`ℚ_ℓ(1) ⊗ ε` of a Tate curve, with Frobenius eigenvalue `ε p` (Silverman, *The Arithmetic of
Elliptic Curves*, Appendix C, §14). The classical factor is read on the inertia *coinvariants*
`V_I = V / ⟨ρ(i) v - v⟩`, on which the arithmetic Frobenius acts by `ε`. The excluded
invariant-space statements are archived in `docs/research/g0-representation-route-invariants.md`.

## Normalization

The corrected readings use the arithmetic Frobenius on inertia coinvariants of the homological
representation (`coinvariantEulerPolynomial`). This is literally Carayol's cohomological
normalization: the same polynomial is the inverse (geometric) Frobenius on the inertia invariants
of the dual representation (`coinvariantEulerPolynomial_eq_dual`, Part H), and the dual of the
dual-normalized representation is `CarayolRationalRealizationCoinv.cohomologicalRep`
(`CarayolRationalRealizationCoinv.local_factor_cohomological`). Locators for the cohomological
normalization: Carayol 1986, §§0.4–0.8, pp. 409–411, as cited by the existing interface (page
bodies not re-checked here).

## Contents

* Part A. `coinvariantEulerPolynomial`, its transport along an isomorphism of representations
  (`coinvariantEulerPolynomial_eq_of_equiv`), its value under trivial inertia
  (`coinvariantEulerPolynomial_of_trivial_inertia`) and under vanishing coinvariants.
* Part B. `localTatePolynomialCoinv`, the corrected polynomial of the actual rational Tate module,
  equal to `localTatePolynomial` whenever inertia acts trivially, in particular at every good
  prime (`localTatePolynomialCoinv_eq_of_trivial_inertia`, `localTatePolynomialCoinv_of_good`).
* Part C. The corrected readings `CarayolRationalRealizationCoinv`,
  `Carayol1986ThmARationalWeightTwoCoinv` and `BadReductionTatePolynomialReadingCoinv`, every
  other field and clause unchanged, and the assembly
  `liCarayolNewformOfModular_of_representations_coinv_of_good`, reusing the Čebotarev–
  Brauer–Nesbitt comparison and the coefficient assembly, with the local transport redone for
  coinvariants.
* Part D. The classical side at bad primes (`localPolynomialQ_of_additive`, `_of_split`,
  `_of_nonsplit`) and the additive case from vanishing coinvariants
  (`localTatePolynomialCoinv_of_additive`).
* Parts E–F. The multiplicative case `localTatePolynomialCoinv_of_multiplicative` from the named
  print `TateCurveTateModulePrint` (Silverman, Appendix C, Theorem C.14.1) and the named glue
  `DecompositionGroupLocalGlobalGlue`. The Tate-module comparison along an embedding
  `\bar ℚ → \bar ℚ_p` (`tateToLocal`, `rationalTateToLocal`) and the computation on a
  representation of Tate-curve shape (`coinvariantEulerPolynomial_of_tateShape`) are proved.
* Part G. `badReductionTatePolynomialReadingCoinv_of_inputs`, the corrected bad-prime reading from
  the print, the glue and the additive-case statement `AdditiveReductionCoinvariantsVanish`,
  which is stated and not proved.
* Part H. Coinvariants against the cohomological normalization.

## Classification

Definitions and PROVED. `TateCurveTateModulePrint` is a reading of a printed theorem (GLUE),
`DecompositionGroupLocalGlobalGlue` and `AdditiveReductionCoinvariantsVanish` are glue, and the
three corrected readings are explicit propositions; all are theorem parameters, not axioms.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GlobalTrace

open Module UpperHalfPlane HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformGlueG0 ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-! ## Part A. Coinvariants of a subgroup and the induced Frobenius -/

section Coinvariants

variable {K G V W : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- **DEFINITION**, the augmentation subspace of a subgroup `I`: the span of the vectors
`ρ(i) v - v` for `i ∈ I`. Locator: the coinvariant quotient of a group representation, as in
Mathlib `Representation.Coinvariants`, restricted to a subgroup. -/
def inertiaAugmentation (ρ : Representation K G V) (I : Subgroup G) : Submodule K V :=
  Submodule.span K {w | ∃ i ∈ I, ∃ v : V, ρ i v - v = w}

/-- **DEFINITION**, the coinvariants `V_I`, the quotient by the augmentation subspace. -/
abbrev inertiaCoinvariants (ρ : Representation K G V) (I : Subgroup G) : Type _ :=
  V ⧸ inertiaAugmentation ρ I

/-- **PROVED**, an element normalizing `I` preserves the augmentation subspace. Locator: the
definition `inertiaAugmentation`. -/
theorem inertiaAugmentation_le_comap (ρ : Representation K G V) (I : Subgroup G) (g : G)
    (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) :
    inertiaAugmentation ρ I ≤ (inertiaAugmentation ρ I).comap (ρ g) := by
  rw [inertiaAugmentation, Submodule.span_le]
  rintro _ ⟨i, hi, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, map_sub]
  apply Submodule.subset_span
  refine ⟨g * i * g⁻¹, hg i hi, ρ g v, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp [mul_assoc]

/-- **DEFINITION**, the action of `g` on the coinvariants `V_I`, for `g` normalizing `I`.
Locator: Mathlib `Submodule.mapQ`. -/
def coinvariantFrobenius (ρ : Representation K G V) (I : Subgroup G) (g : G)
    (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) : Module.End K (inertiaCoinvariants ρ I) :=
  (inertiaAugmentation ρ I).mapQ (inertiaAugmentation ρ I) (ρ g)
    (inertiaAugmentation_le_comap ρ I g hg)

/-- **PROVED**, the induced action on a class. Locator: Mathlib `Submodule.mapQ_apply`. -/
theorem coinvariantFrobenius_mk (ρ : Representation K G V) (I : Subgroup G) (g : G)
    (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) (v : V) :
    coinvariantFrobenius ρ I g hg (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) :=
  rfl

/-- **DEFINITION**, the local Euler polynomial on coinvariants: the reversed characteristic
polynomial of `g` acting on `V_I`. With `g` an arithmetic Frobenius and the homological
normalization, this is the classical local factor (module documentation). -/
def coinvariantEulerPolynomial [FiniteDimensional K V] (ρ : Representation K G V)
    (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) : Polynomial K :=
  (LinearMap.charpoly (coinvariantFrobenius ρ I g hg)).reverse

/-- **PROVED**, an isomorphism of representations carries the augmentation subspace onto the
augmentation subspace. Locator: the intertwining property `IntertwiningMap.isIntertwining`. -/
theorem map_inertiaAugmentation {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G) :
    (inertiaAugmentation ρ I).map (e.toLinearEquiv : V →ₗ[K] W) = inertiaAugmentation σ I := by
  have hint : ∀ (g : G) (v : V), e (ρ g v) = σ g (e v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v
  rw [inertiaAugmentation, inertiaAugmentation, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨i, hi, v, rfl⟩, rfl⟩
    exact ⟨i, hi, e v, by
      change σ i (e v) - e v = e (ρ i v - v)
      rw [map_sub, hint]⟩
  · rintro ⟨i, hi, w', rfl⟩
    refine ⟨ρ i (e.symm w') - e.symm w', ⟨i, hi, e.symm w', rfl⟩, ?_⟩
    change e (ρ i (e.symm w') - e.symm w') = σ i w' - w'
    have h : e (e.symm w') = w' := e.apply_symm_apply w'
    rw [map_sub, hint, h]

/-- **DEFINITION WITH PROVED INVERSE**, the isomorphism of coinvariants induced by an isomorphism
of representations. Locator: Mathlib `Submodule.Quotient.equiv`. -/
def coinvariantsEquiv {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G) :
    inertiaCoinvariants ρ I ≃ₗ[K] inertiaCoinvariants σ I :=
  Submodule.Quotient.equiv _ _ e.toLinearEquiv (map_inertiaAugmentation e I)

/-- **PROVED**, the induced isomorphism of coinvariants conjugates the two Frobenius actions.
Locator: the intertwining property. -/
theorem coinvariantFrobenius_conj {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) :
    (coinvariantsEquiv e I).conj (coinvariantFrobenius ρ I g hg) =
      coinvariantFrobenius σ I g hg := by
  have hint : ∀ (g : G) (v : V), e (ρ g v) = σ g (e v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v
  apply LinearMap.ext
  intro x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearEquiv.conj_apply_apply]
  have h1 : (coinvariantsEquiv e I).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (e.symm w) := rfl
  rw [h1, coinvariantFrobenius_mk, coinvariantFrobenius_mk]
  change Submodule.Quotient.mk (e (ρ g (e.symm w))) = Submodule.Quotient.mk (σ g w)
  have h : e (e.symm w) = w := e.apply_symm_apply w
  rw [hint, h]

/-- **PROVED**, an isomorphism of representations preserves the coinvariant Euler polynomial.
Locators: `coinvariantFrobenius_conj`, Mathlib `LinearEquiv.charpoly_conj`. This is the
coinvariant analogue of `NewformGlueG0.inertiaEulerPolynomial_eq_of_equiv`. -/
theorem coinvariantEulerPolynomial_eq_of_equiv [FiniteDimensional K V] [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W} (e : Representation.Equiv ρ σ)
    (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) :
    coinvariantEulerPolynomial ρ I g hg = coinvariantEulerPolynomial σ I g hg := by
  unfold coinvariantEulerPolynomial
  rw [← coinvariantFrobenius_conj e I g hg, LinearEquiv.charpoly_conj]

/-- **PROVED**, trivial action of `I` gives a zero augmentation subspace. -/
theorem inertiaAugmentation_eq_bot (ρ : Representation K G V) (I : Subgroup G)
    (hI : ∀ i ∈ I, ρ i = 1) : inertiaAugmentation ρ I = ⊥ := by
  rw [inertiaAugmentation, Submodule.span_eq_bot]
  rintro _ ⟨i, hi, v, rfl⟩
  rw [hI i hi, Module.End.one_apply, sub_self]

/-- **PROVED**, under trivial action of `I` the coinvariant polynomial is the full reversed
characteristic polynomial. Locators: `inertiaAugmentation_eq_bot`, Mathlib
`Submodule.quotEquivOfEqBot` and `LinearEquiv.charpoly_conj`. -/
theorem coinvariantEulerPolynomial_of_trivial_inertia [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I)
    (hI : ∀ i ∈ I, ρ i = 1) :
    coinvariantEulerPolynomial ρ I g hg = (LinearMap.charpoly (ρ g)).reverse := by
  let e := Submodule.quotEquivOfEqBot _ (inertiaAugmentation_eq_bot ρ I hI)
  have hc : e.conj (coinvariantFrobenius ρ I g hg) = ρ g := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change e (coinvariantFrobenius ρ I g hg (Submodule.Quotient.mk v)) = ρ g v
    rw [coinvariantFrobenius_mk]
    rfl
  unfold coinvariantEulerPolynomial
  rw [← hc, LinearEquiv.charpoly_conj]

/-- **PROVED**, vanishing coinvariants give the constant polynomial `1`. Locators: Mathlib
`Submodule.subsingleton_quotient_iff_eq_top`, `LinearMap.charpoly_natDegree`. -/
theorem coinvariantEulerPolynomial_of_augmentation_eq_top [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I)
    (h : inertiaAugmentation ρ I = ⊤) : coinvariantEulerPolynomial ρ I g hg = 1 := by
  have : Subsingleton (inertiaCoinvariants ρ I) :=
    Submodule.Quotient.subsingleton_iff.mpr h
  have hc : LinearMap.charpoly (coinvariantFrobenius ρ I g hg) = 1 := by
    apply Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]
  unfold coinvariantEulerPolynomial
  rw [hc, ← Polynomial.C_1, Polynomial.reverse_C]

end Coinvariants

/-! ## Part B. The corrected local polynomial of the actual rational Tate module -/

section TateCoinvariants

/-- **PROVED**, the decomposition group normalizes the actual inertia subgroup in the direction
used by coinvariants: `g i g⁻¹ ∈ I`. Locator: normality of `ValuationSubring.inertiaSubgroup` in
the decomposition group, as in `Completion.inertiaAt_normalized`. -/
theorem inertiaAt_conj {p : ℕ} (D : LocalArithmeticFrobenius p) :
    ∀ i ∈ inertiaAt D, D.element * i * D.element⁻¹ ∈ inertiaAt D := by
  intro i hi
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hi
  let g : D.place.decompositionSubgroup ℚ := ⟨D.element, D.isFrob.1⟩
  have hn : (D.place.inertiaSubgroup ℚ).Normal := by
    unfold ValuationSubring.inertiaSubgroup
    infer_instance
  exact Subgroup.mem_map.mpr ⟨g * s * g⁻¹, hn.conj_mem s hs g, rfl⟩

/-- **DEFINITION**, the corrected local Tate polynomial: the arithmetic Frobenius `D.element`
on the inertia coinvariants of the actual rational Tate module `ℚ_ℓ ⊗ T_ℓ(E)`. Locators:
`coinvariantEulerPolynomial`; Silverman, Appendix C, §14 and §16, for the classical factor it is
meant to read. -/
def localTatePolynomialCoinv (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    {p : ℕ} (D : LocalArithmeticFrobenius p) : Polynomial ℚ_[ℓ] :=
  coinvariantEulerPolynomial (rationalTateRep E ℓ) (inertiaAt D) D.element (inertiaAt_conj D)

/-- **PROVED**, under trivial inertia the corrected polynomial is the existing
`localTatePolynomial`: both are the reversed characteristic polynomial of Frobenius on the whole
module. Locators: `coinvariantEulerPolynomial_of_trivial_inertia`,
`Completion.inertiaEulerPolynomial_of_trivial_inertia`. -/
theorem localTatePolynomialCoinv_eq_of_trivial_inertia (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p)
    (hI : ∀ i ∈ inertiaAt D, rationalTateRep E ℓ i = 1) :
    localTatePolynomialCoinv E ℓ D = localTatePolynomial E ℓ D := by
  rw [localTatePolynomialCoinv, coinvariantEulerPolynomial_of_trivial_inertia _ _ _ _ hI,
    localTatePolynomial, inertiaEulerPolynomial_of_trivial_inertia _ _ _ _ hI]

/-- **PROVED FROM THE GOOD-PRIME READING**, at a good prime `p ≠ ℓ` the corrected polynomial is
the existing one and equals the minimal-reduction polynomial: nothing changes at good primes.
Locators: `localTatePolynomialCoinv_eq_of_trivial_inertia`, `Completion.localTatePolynomial_of_good`.
The reading is proved as `GlobalTrace.globalGoodReductionTraceReading_proved`
(`GlobalTrace/GoodReductionReading.lean`). -/
theorem localTatePolynomialCoinv_of_good (hG : GlobalGoodReductionTraceReading)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (hgood : GoodReductionAt E (primeIdealQ p hp)) (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) := by
  rw [localTatePolynomialCoinv_eq_of_trivial_inertia E ℓ D
    ((hG goodReductionFrobeniusTraceDictionaryQ_proved E ℓ p hp hpℓ hgood).1 D)]
  exact localTatePolynomial_of_good hG E ℓ p hp hpℓ hgood D

end TateCoinvariants

/-! ## Part C. The corrected readings and the representation assembly -/

section CorrectedReadings

/-- **DEFINITION OF PRINTED DATA, CORRECTED LOCAL READING**, a normalized representation
attached to an actual rational weight-two newform. The four fields `normalizedRep`,
`continuous_matrix`, `irreducible` and `good_trace` have their original types. The local-factor
field reads the Euler polynomial on inertia coinvariants with arithmetic Frobenius
(`coinvariantEulerPolynomial`), equivalently on the inertia invariants of the cohomological
normalization with geometric Frobenius. The excluded invariant-space realization is archived in
`docs/research/g0-representation-route-invariants.md`. Locators: Carayol 1986, (A), pp. 410–411,
the Remarque p. 411, §0.8; Li 1975, Theorem 3(i), p. 295; Casselman 1973, Theorem 4, p. 313
(page bodies not re-checked here). -/
structure CarayolRationalRealizationCoinv {M : ℕ} [NeZero M]
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
  /-- **PRINTED GOOD-PRIME READING**, arithmetic trace. Locator: Carayol §§0.5–0.7,
  pp. 410–411. -/
  good_trace : ∀ (p : ℕ), p.Prime → ¬p ∣ M * ℓ →
    ∀ g : GlueC10.GQ, GlueC10.IsFrobAt g p →
      LinearMap.trace ℚ_[ℓ] (Fin 2 → ℚ_[ℓ]) (normalizedRep g) = (b p : ℚ_[ℓ])
  /-- **CORRECTED CONSEQUENCE OF PRINTED LOCAL COMPATIBILITY**, at every `p ≠ ℓ`, on inertia
  coinvariants with the arithmetic Frobenius. Locators: Carayol (A), pp. 410–411; Li
  Theorem 3(i), p. 295; Casselman Theorem 4, p. 313. -/
  local_factor : ∀ (p : ℕ), p.Prime → p ≠ ℓ → ∀ D : LocalArithmeticFrobenius p,
    coinvariantEulerPolynomial normalizedRep (inertiaAt D) D.element (inertiaAt_conj D) =
      rationalNewformPolynomial M ℓ b p

/-- **DEFINITION**, Carayol's cohomological normalization is the dual of the normalized
representation used for the coinvariant Tate comparison. Locators: Carayol §§0.4–0.5 and §0.8,
pp. 409–411. Its invariant polynomial with geometric Frobenius is proved to be the coinvariant
polynomial with arithmetic Frobenius in `coinvariantEulerPolynomial_eq_dual`. The historical
invariant-space realization is recorded in `docs/research/g0-representation-route-invariants.md`. -/
def CarayolRationalRealizationCoinv.cohomologicalRep {M : ℕ} [NeZero M]
    {F : Newform M 2} {hχ : F.χ = 1} {b : ℕ → ℚ}
    {hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ)}
    {ℓ : ℕ} [Fact ℓ.Prime] (R : CarayolRationalRealizationCoinv F hχ b hb ℓ) :
    Representation ℚ_[ℓ] GlueC10.GQ (Module.Dual ℚ_[ℓ] (Fin 2 → ℚ_[ℓ])) :=
  R.normalizedRep.dual

/-- **GLUE (a reading of Carayol's theorem) WITH CORRECTED LOCAL READING**, the rational weight-two
realization with arithmetic Frobenius on inertia coinvariants. The excluded invariant-space
statement is archived in `docs/research/g0-representation-route-invariants.md`. Locators: Carayol
1986, Théorème (A), pp. 410–411, Remarque and §0.8, p. 411; Casselman 1973, Theorem 4, p. 313; Li
1975, Theorem 3(i), p. 295. This is a proposition, not an axiom or a proof of these printed facts.
-/
def Carayol1986ThmARationalWeightTwoCoinv : Prop :=
  ∀ (M : ℕ) [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime], Nonempty (CarayolRationalRealizationCoinv F hχ b hb ℓ)

/-- **GLUE, CORRECTED BAD-PRIME TATE LOCAL READING**, at a bad prime `p ≠ ℓ` the
minimal-reduction polynomial is the arithmetic Frobenius polynomial on the inertia coinvariants
of the actual rational Tate module. The excluded invariant-space statement is archived in
`docs/research/g0-representation-route-invariants.md`. Locators: Silverman, Appendix C, §14
(Tate curves, multiplicative reduction) and §16 (local factors), VII.5–VII.7 (additive reduction);
section-level, pages not checked. Its reduction to the named inputs is
`badReductionTatePolynomialReadingCoinv_of_inputs` (Parts D–G). -/
def BadReductionTatePolynomialReadingCoinv : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (p : ℕ) (hp : p.Prime), p ≠ ℓ → ¬GoodReductionAt E (primeIdealQ p hp) →
      ∀ D : LocalArithmeticFrobenius p,
        localTatePolynomialCoinv E ℓ D =
          (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ])

/-- **PROVED FROM THE PRINTED SEMISIMPLICITY AND THE GOOD-PRIME READING**, the comparison of
the actual rational Tate representation with any continuous irreducible representation having
the newform traces at good Frobenius elements. Only continuity, irreducibility and good traces
of that representation are used; no bad-prime local-factor reading is consumed. The historical
realization-specific comparison is archived in
`docs/research/g0-representation-route-invariants.md`. Locators:
`representationEquiv_of_BN_frobenius`, `brauerNesbittChar0`, Faltings Satz 3, p. 360. -/
theorem tate_equiv_of_good_traces
    (hFa : Faltings1983Satz3EllipticQ) (hG : GlobalGoodReductionTraceReading)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (S : Finset ℕ) (hFp : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Representation ℚ_[ℓ] GlueC10.GQ (Fin 2 → ℚ_[ℓ]))
    (hσc : Continuous fun g : GlueC10.GQ =>
      LinearMap.toMatrix (Pi.basisFun ℚ_[ℓ] (Fin 2)) (Pi.basisFun ℚ_[ℓ] (Fin 2)) (σ g))
    (hσi : σ.IsIrreducible)
    (hσt : ∀ (p : ℕ), p.Prime → ¬p ∣ M * ℓ →
      ∀ g : GlueC10.GQ, GlueC10.IsFrobAt g p →
        LinearMap.trace ℚ_[ℓ] (Fin 2 → ℚ_[ℓ]) (σ g) = (b p : ℚ_[ℓ])) :
    Nonempty (Representation.Equiv (rationalTateRep E ℓ) σ) := by
  classical
  have hEr : IsSemisimpleModule (MonoidAlgebra ℚ_[ℓ] GlueC10.GQ)
      (rationalTateRep E ℓ).asModule := hFa E ℓ
  have hR : σ.IsIrreducible := hσi
  have hRs : IsSemisimpleModule (MonoidAlgebra ℚ_[ℓ] GlueC10.GQ) σ.asModule :=
    inferInstance
  obtain ⟨T, hT⟩ := goodReductionAt_almost_all_primes E inferInstance
  apply representationEquiv_of_BN_frobenius brauerNesbittChar0 ℚ_[ℓ]
    (rationalTate E ℓ) (Fin 2 → ℚ_[ℓ]) (Fin 2) (Fin 2)
    (rationalTateBasis E ℓ) (Pi.basisFun ℚ_[ℓ] (Fin 2))
    (rationalTateRep E ℓ) σ (continuous_rationalTateRep_matrix E ℓ)
    hσc hEr hRs ((S ∪ T) ∪ (M * ℓ).primeFactors)
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
  rw [hgE.1, hσt p hp hpMℓ g hg]
  have hbp : b p = (E.LFunction p : ℚ) := by
    have h := (hb p).symm.trans (hFp p hp hpS)
    exact_mod_cast h
  rw [hbp, Rat.cast_intCast]

/-- **PROVED**, the comparison transports the corrected local polynomial at every `p ≠ ℓ`,
including bad primes. Locators: `tate_equiv_of_good_traces`,
`coinvariantEulerPolynomial_eq_of_equiv` (the local transport redone for coinvariants), and the
field `CarayolRationalRealizationCoinv.local_factor`. -/
theorem localTatePolynomialCoinv_eq_newform_of_comparison
    (hFa : Faltings1983Satz3EllipticQ) (hG : GlobalGoodReductionTraceReading)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1) (b : ℕ → ℚ)
    (hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ))
    (S : Finset ℕ) (hFp : ∀ p : ℕ, p.Prime → p ∉ S →
      (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ))
    (ℓ : ℕ) [Fact ℓ.Prime] (R : CarayolRationalRealizationCoinv F hχ b hb ℓ)
    (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ) (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D = rationalNewformPolynomial M ℓ b p := by
  obtain ⟨e⟩ := tate_equiv_of_good_traces hFa hG E F b hb S hFp ℓ R.normalizedRep
    R.continuous_matrix R.irreducible R.good_trace
  exact (coinvariantEulerPolynomial_eq_of_equiv e (inertiaAt D) D.element
    (inertiaAt_conj D)).trans (R.local_factor p hp hpℓ D)

/-- **PROVED CONDITIONAL REPRESENTATION ASSEMBLY ON COINVARIANTS**, the exact G0 conclusion from
the corrected readings. The representation comparison, local coinvariant transport, auxiliary-
prime avoidance and coefficient assembly are proved below. The excluded invariant-space
assembly is archived in `docs/research/g0-representation-route-invariants.md`. The good-prime
reading `hG` is proved as `GlobalTrace.globalGoodReductionTraceReading_proved`; the instantiation
without it is `GlobalTrace.liCarayolNewformOfModular_of_representations_coinv`
(`GlobalTrace/CoinvariantAssembly.lean`). Locators: Carayol (A) and §0.8, pp. 410–411;
Faltings Satz 3, p. 360; Shimura Theorem 1, p. 526; Li Theorem 5, p. 298. -/
theorem liCarayolNewformOfModular_of_representations_coinv_of_good
    (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
    (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986ThmARationalWeightTwoCoinv) (hFa : Faltings1983Satz3EllipticQ)
    (hG : GlobalGoodReductionTraceReading) (hB : BadReductionTatePolynomialReadingCoinv) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular := by
  classical
  intro E hE N hN f hf
  have : E.IsElliptic := hE
  obtain ⟨M, hM0, F, hMN, hχ, S, hFp⟩ :=
    exists_newform_almost_all_prime_coeff E hE N hN f hf
  have hrat :=
    ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.coefficients_rational_of_almost_all_primes
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
    have hcompare := localTatePolynomialCoinv_eq_newform_of_comparison
      hFa hG E F hχ b hb S hFp ℓ R p hp hpℓ D
    have hT : localTatePolynomialCoinv E ℓ D =
        (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) := by
      by_cases hgood : GoodReductionAt E (primeIdealQ p hp)
      · exact localTatePolynomialCoinv_of_good hG E ℓ p hp hpℓ hgood D
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

end CorrectedReadings

/-! ## Part D. The corrected bad-prime reading: the classical side and the additive case -/

section BadPrimes

open Polynomial

/-- **PROVED**, the existing local polynomial at a prime of additive reduction is `1`: the minimal
model has neither good nor multiplicative reduction. Locator: the definition
`WeierstrassCurve.localPolynomial`. -/
theorem localPolynomialQ_of_additive (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (hgood : ¬GoodReductionAt E (primeIdealQ p hp))
    (hmult : ¬((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)) :
    localPolynomialQ E (primeIdealQ p hp) = 1 := by
  have hsplit : ¬((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ) := fun h => hmult h.toHasMultiplicativeReduction
  rw [GoodReductionAt] at hgood
  simp only [localPolynomialQ, WeierstrassCurve.localPolynomial, hgood, hsplit, hmult,
    ↓reduceIte]

/-- **PROVED**, the existing local polynomial at a prime of split multiplicative reduction is
`1 - X`. Locator: the definition `WeierstrassCurve.localPolynomial`. -/
theorem localPolynomialQ_of_split (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (hsplit : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)) :
    localPolynomialQ E (primeIdealQ p hp) = 1 - X := by
  have hgood : ¬GoodReductionAt E (primeIdealQ p hp) := fun h =>
    (WeierstrassCurve.HasMultiplicativeReduction.not_hasGoodReduction _
      hsplit.toHasMultiplicativeReduction) h
  rw [GoodReductionAt] at hgood
  simp only [localPolynomialQ, WeierstrassCurve.localPolynomial, hgood, hsplit, ↓reduceIte]

/-- **PROVED**, the existing local polynomial at a prime of non-split multiplicative reduction is
`1 + X`. Locator: the definition `WeierstrassCurve.localPolynomial`. -/
theorem localPolynomialQ_of_nonsplit (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (hmult : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ))
    (hsplit : ¬((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)) :
    localPolynomialQ E (primeIdealQ p hp) = 1 + X := by
  have hgood : ¬GoodReductionAt E (primeIdealQ p hp) := fun h =>
    (WeierstrassCurve.HasMultiplicativeReduction.not_hasGoodReduction _ hmult) h
  rw [GoodReductionAt] at hgood
  simp only [localPolynomialQ, WeierstrassCurve.localPolynomial, hgood, hsplit, hmult,
    ↓reduceIte]

/-- **PROVED**, the additive case of `BadReductionTatePolynomialReadingCoinv` reduces exactly to
the vanishing of the inertia coinvariants of the actual rational Tate module: both sides are then
`1`. Locators: `coinvariantEulerPolynomial_of_augmentation_eq_top`, `localPolynomialQ_of_additive`.
The vanishing itself is not assumed anywhere in this module. -/
theorem localTatePolynomialCoinv_of_additive (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
    [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime) (hgood : ¬GoodReductionAt E (primeIdealQ p hp))
    (hmult : ¬((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ))
    (D : LocalArithmeticFrobenius p)
    (hzero : inertiaAugmentation (rationalTateRep E ℓ) (inertiaAt D) = ⊤) :
    localTatePolynomialCoinv E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) := by
  rw [localTatePolynomialCoinv, coinvariantEulerPolynomial_of_augmentation_eq_top _ _ _ _ hzero,
    localPolynomialQ_of_additive E p hp hgood hmult, Polynomial.map_one]

end BadPrimes

/-! ## Part E. Two linear-algebra lemmas for the multiplicative case -/

section LinearAlgebra

open Polynomial

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- **PROVED**, the coinvariant polynomial depends only on the augmentation subspace and on the
linear map of the Frobenius element, so it may be computed through a different group acting
through the same operators. Locators: Mathlib `Submodule.quotEquivOfEq`,
`LinearEquiv.charpoly_conj`. -/
theorem coinvariantEulerPolynomial_congr [FiniteDimensional K V] {G' : Type*} [Group G']
    (ρ : Representation K G V) (ρ' : Representation K G' V) (I : Subgroup G) (I' : Subgroup G')
    (g : G) (g' : G') (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I) (hg' : ∀ i ∈ I', g' * i * g'⁻¹ ∈ I')
    (hA : inertiaAugmentation ρ I = inertiaAugmentation ρ' I') (hgg : ρ g = ρ' g') :
    coinvariantEulerPolynomial ρ I g hg = coinvariantEulerPolynomial ρ' I' g' hg' := by
  let e := Submodule.quotEquivOfEq _ _ hA
  have hc : e.conj (coinvariantFrobenius ρ I g hg) = coinvariantFrobenius ρ' I' g' hg' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearEquiv.conj_apply_apply]
    change e (coinvariantFrobenius ρ I g hg (Submodule.Quotient.mk v)) =
      coinvariantFrobenius ρ' I' g' hg' (Submodule.Quotient.mk v)
    rw [coinvariantFrobenius_mk, coinvariantFrobenius_mk, hgg]
    rfl
  unfold coinvariantEulerPolynomial
  rw [← hc, LinearEquiv.charpoly_conj]

/-- **PROVED**, the augmentation subspace of a representation pulled back along a group
homomorphism is that of the image subgroup. Locator: Mathlib `Subgroup.mem_map`. -/
theorem inertiaAugmentation_comp {H : Type*} [Group H] (ρ : Representation K G V) (r : H →* G)
    (J : Subgroup H) : inertiaAugmentation (ρ.comp r) J = inertiaAugmentation ρ (J.map r) := by
  rw [inertiaAugmentation, inertiaAugmentation]
  congr 1
  ext w
  constructor
  · rintro ⟨j, hj, v, rfl⟩
    exact ⟨r j, Subgroup.mem_map_of_mem r hj, v, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, v, rfl⟩
    exact ⟨j, hj, v, rfl⟩

/-- **PROVED**, the reversal of a linear factor. Locators: Mathlib `Polynomial.reverse_add_C`,
`Polynomial.reverse_mul_X`. -/
theorem reverse_X_sub_C' (c : K) : (X - C c : Polynomial K).reverse = 1 - C c * X := by
  rw [sub_eq_add_neg, ← map_neg C c, reverse_add_C, natDegree_X, pow_one]
  have hX : (X : Polynomial K).reverse = 1 := by
    have h := reverse_mul_X (1 : Polynomial K)
    rw [one_mul] at h
    rw [h, ← C_1, reverse_C]
  rw [hX, map_neg, neg_mul, ← sub_eq_add_neg]

/-- **PROVED**, the coinvariant polynomial of a representation of Tate-curve shape: in a basis
`(e₀, e₁)` with `h e₀ = ε(h) χ(h) e₀` and `h e₁ = ε(h) (e₁ + κ(h) e₀)`, where `ε` and `χ` are
trivial on `I` and `κ` is not identically zero on `I`, the coinvariants are the line spanned by
the class of `e₁`, the augmentation being the line of `e₀`, and `g` acts on them by `ε(g)`; so
the polynomial is `1 - ε(g) X`. Locators: Mathlib `Submodule.finrank_quotient_add_finrank`,
`finrank_span_singleton`, `Matrix.charpoly_diagonal`. -/
theorem coinvariantEulerPolynomial_of_tateShape [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I)
    (b : Basis (Fin 2) K V) (ε χ κ : G → K)
    (h0 : ∀ h, ρ h (b 0) = (ε h * χ h) • b 0) (h1 : ∀ h, ρ h (b 1) = ε h • (b 1 + κ h • b 0))
    (hI : ∀ i ∈ I, ε i = 1 ∧ χ i = 1) (hκ : ∃ i ∈ I, κ i ≠ 0) :
    coinvariantEulerPolynomial ρ I g hg = 1 - C (ε g) * X := by
  have hdec : ∀ v : V, v = b.repr v 0 • b 0 + b.repr v 1 • b 1 := by
    intro v
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two]
  -- the augmentation subspace is the line of `e₀`
  have hA : inertiaAugmentation ρ I = K ∙ b 0 := by
    apply le_antisymm
    · rw [inertiaAugmentation, Submodule.span_le]
      rintro _ ⟨i, hi, v, rfl⟩
      obtain ⟨hεi, hχi⟩ := hI i hi
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨b.repr v 1 * κ i, ?_⟩
      conv_rhs => rw [hdec v]
      rw [map_add, map_smul, map_smul, h0, h1, hεi, hχi]
      module
    · rw [Submodule.span_singleton_le_iff_mem]
      obtain ⟨i₀, hi₀, hκ₀⟩ := hκ
      have hmem : ρ i₀ (b 1) - b 1 ∈ inertiaAugmentation ρ I :=
        Submodule.subset_span ⟨i₀, hi₀, b 1, rfl⟩
      have hval : ρ i₀ (b 1) - b 1 = κ i₀ • b 0 := by
        rw [h1, (hI i₀ hi₀).1, one_smul]
        abel
      rw [hval] at hmem
      have := Submodule.smul_mem _ (κ i₀)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hκ₀, one_smul] at this
  -- `g` acts on the coinvariants by `ε g`
  have hF : coinvariantFrobenius ρ I g hg = ε g • (1 : Module.End K (inertiaCoinvariants ρ I)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [coinvariantFrobenius_mk, LinearMap.smul_apply, Module.End.one_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hA, Submodule.mem_span_singleton]
    refine ⟨b.repr v 0 * (ε g * χ g - ε g) + b.repr v 1 * (ε g * κ g), ?_⟩
    conv_rhs => rw [hdec v]
    rw [map_add, map_smul, map_smul, h0, h1]
    module
  -- the coinvariants are one-dimensional
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  have hfA : Module.finrank K (inertiaAugmentation ρ I) = 1 := by
    rw [(LinearEquiv.ofEq _ _ hA).finrank_eq, finrank_span_singleton hb0]
  have hdim : Module.finrank K (inertiaCoinvariants ρ I) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank (inertiaAugmentation ρ I)
    rw [hfA, Module.finrank_eq_card_basis b, Fintype.card_fin] at h
    change Module.finrank K (V ⧸ inertiaAugmentation ρ I) = 1
    omega
  let c := Module.finBasisOfFinrankEq K (inertiaCoinvariants ρ I) hdim
  have hchar : LinearMap.charpoly (coinvariantFrobenius ρ I g hg) = X - C (ε g) := by
    rw [← LinearMap.charpoly_toMatrix _ c, hF, map_smul, LinearMap.toMatrix_one,
      Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_one]
  unfold coinvariantEulerPolynomial
  rw [hchar, reverse_X_sub_C']

end LinearAlgebra

/-! ## Part F. The multiplicative case from a named print and a named glue statement -/

section Multiplicative

open scoped Classical WithZero
open Polynomial WeierstrassCurve

/-- **DEFINITION**, the local Galois group `Gal(\bar ℚ_p / ℚ_p)`, for the algebraic closure of the
completion at `p` used by the local dictionary. -/
abbrev LocalGaloisQ (p : ℕ) (hp : p.Prime) : Type :=
  AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ) ≃ₐ[(primeIdealQ p hp).adicCompletion ℚ]
    AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)

/-- **DEFINITION**, the inertia subgroup of a valuation of `\bar ℚ_p` in the local Galois group:
the kernel of the residue-field action in the decomposition group, as in `Completion.inertiaAt`.
Locator: Mathlib `ValuationSubring.inertiaSubgroup`. -/
def localInertia {p : ℕ} {hp : p.Prime} {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ) :
    Subgroup (LocalGaloisQ p hp) :=
  (w.valuationSubring.inertiaSubgroup ((primeIdealQ p hp).adicCompletion ℚ)).map
    (w.valuationSubring.decompositionSubgroup ((primeIdealQ p hp).adicCompletion ℚ)).subtype

/-- **GLUE, LOCAL–GLOBAL DECOMPOSITION GROUPS**, the identification of the decomposition group of a
place of `\bar ℚ` above `p` with the local Galois group `Gal(\bar ℚ_p / ℚ_p)`: for every place
`D.place` above `p` with arithmetic Frobenius `D.element` there are a valuation `w` of `\bar ℚ_p`
extending the `p`-adic valuation, an embedding `ι : \bar ℚ → \bar ℚ_p` and the restriction
homomorphism `r : Gal(\bar ℚ_p / ℚ_p) → Gal(\bar ℚ / ℚ)`, `ι ∘ r(σ) = σ ∘ ι`, carrying the inertia
group of `w` onto the inertia group of `D.place` and some local arithmetic Frobenius to
`D.element`. Standard algebraic number theory (the restriction is an isomorphism onto the
decomposition group, compatible with inertia), absent from Mathlib for the infinite extension
`\bar ℚ / ℚ`; not a statement of the manuscript-cited sources, and not proved here. It says nothing
about elliptic curves. -/
def DecompositionGroupLocalGlobalGlue : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (D : LocalArithmeticFrobenius p),
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
      (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
      (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
      (r : LocalGaloisQ p hp →* GlueC10.GQ),
      (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
          (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
        (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) ∧
      (∀ (σ : LocalGaloisQ p hp) (x : AlgebraicClosure ℚ), ι (r σ x) = σ (ι x)) ∧
      (localInertia w).map r = inertiaAt D ∧
      ∃ σ : LocalGaloisQ p hp,
        IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ ∧ r σ = D.element

/-- **GLUE (a reading of a printed theorem) WITH DERIVED READINGS**, manuscript bibitem Silverman,
*The Arithmetic of Elliptic Curves*, Appendix C, Theorem C.14.1 (Tate), read on the local `ℓ`-adic
Tate module. For `E/ℚ` with
multiplicative reduction at `p` and `ℓ ≠ p`, Tate's theorem gives `q ∈ ℚ_p` with `|q| < 1` and a
Galois-equivariant uniformization `\bar ℚ_p^× / q^ℤ ≅ E(\bar ℚ_p)` (over `ℚ_p` in the split case,
after the unramified quadratic twist in the non-split case). Read through Kummer theory this gives a
basis `(e₀, e₁)` of `T_ℓ(E/\bar ℚ_p)` (`e₀` the roots of unity, `e₁` the compatible roots of `q`)
with `σ e₀ = ε(σ) χ(σ) e₀` and `σ e₁ = ε(σ) (e₁ + κ(σ) e₀)`, where `χ` is the cyclotomic character,
`κ` the Kummer cocycle of `q`, and `ε` is trivial in the split case and the unramified quadratic
character otherwise. The readings used: `ε` and `χ` are trivial on inertia, `κ` is not identically
zero on inertia (`v(q) ≠ 0`), and `ε` of an arithmetic Frobenius is `1` or `-1` according as the
reduction is split or not. Section-level locator; page not checked. The unramified twist in the
non-split case and the Kummer description of the Tate module are derived readings, not literal
statements of C.14.1. This is a proposition, not an axiom or a proof of the printed theorem. -/
def TateCurveTateModulePrint : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) (hp : p.Prime) (ℓ : ℕ) [Fact ℓ.Prime],
    ℓ ≠ p →
    ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ) →
    ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
      (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
      (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
          (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
        (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
      ∃ (b : Basis (Fin 2) ℤ_[ℓ] (TauCeti.TateModule ℓ
          ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
            (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point))
        (ε χ κ : LocalGaloisQ p hp → ℤ_[ℓ]),
        (∀ σ, (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation
          ℓ σ (b 0) = (ε σ * χ σ) • b 0) ∧
        (∀ σ, (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation
          ℓ σ (b 1) = ε σ • (b 1 + κ σ • b 0)) ∧
        (∀ σ ∈ localInertia w, ε σ = 1 ∧ χ σ = 1) ∧
        (∃ σ ∈ localInertia w, κ σ ≠ 0) ∧
        ∀ σ, IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ →
          ε σ = if ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
            ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
              ((primeIdealQ p hp).adicCompletionIntegers ℚ) then 1 else -1

variable (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)

/-- **PROVED**, the curve over `\bar ℚ_p` obtained through `ℚ_p` is the base change of `E`.
Locator: Mathlib `WeierstrassCurve.map_baseChange`. -/
theorem baseChange_completion_closure :
    (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) =
      E.baseChange (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) :=
  WeierstrassCurve.map_baseChange (W := E)
    (IsScalarTower.toAlgHom ℚ ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))

/-- **DEFINITION**, base change of points along an embedding `ι : \bar ℚ → \bar ℚ_p`. Locators:
Tau Ceti `Affine.Point.map` and transport along `baseChange_completion_closure`. -/
def pointsToLocal
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) :
    (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point →+
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) => V.toAffine.Point)
    (baseChange_completion_closure E p hp).symm).toAddMonoidHom.comp
    (Affine.Point.map (W' := E) ι)

/-- **PROVED**, base change of points along an embedding is injective. Locator: Mathlib
`WeierstrassCurve.Affine.Point.map_injective`. -/
theorem pointsToLocal_injective
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) :
    Function.Injective (pointsToLocal E p hp ι) := by
  rw [pointsToLocal, AddMonoidHom.coe_comp]
  exact (AddEquiv.injective _).comp (Affine.Point.map_injective ι)

/-- **PROVED**, base change of points is equivariant for the restriction `r`:
`ι ∘ r(σ) = σ ∘ ι` moves coordinates compatibly. Locator: Tau Ceti `Affine.Point.map_some`. -/
theorem pointsToLocal_map
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (r : LocalGaloisQ p hp →* GlueC10.GQ)
    (hres : ∀ (σ : LocalGaloisQ p hp) (x : AlgebraicClosure ℚ), ι (r σ x) = σ (ι x))
    (σ : LocalGaloisQ p hp) (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    pointsToLocal E p hp ι (Affine.Point.map (W' := E) (r σ).toAlgHom P) =
      Affine.Point.map (W' := E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)) σ.toAlgHom
        (pointsToLocal E p hp ι P) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← Affine.Point.zero_def, map_zero]
  · simp only [pointsToLocal, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      Affine.Point.map_some]
    rw [AddEquiv.cast_apply (baseChange_completion_closure E p hp).symm,
      Affine.Point.cast_some (baseChange_completion_closure E p hp).symm,
      AddEquiv.cast_apply (baseChange_completion_closure E p hp).symm,
      Affine.Point.cast_some (baseChange_completion_closure E p hp).symm, Affine.Point.map_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hres σ x, hres σ y⟩

/-- **PROVED**, base change of points is a bijection on `ℓⁿ`-torsion: it is injective, and both
torsion groups have `(ℓⁿ)²` elements over the two separably closed fields of characteristic zero.
Locators: `pointsToLocal_injective`, Tau Ceti `WeierstrassCurve.natCard_tateModuleLevel`. -/
theorem levelMap_pointsToLocal_bijective [E.IsElliptic]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Function.Bijective (TauCeti.TateModule.levelMap (p := ℓ) (pointsToLocal E p hp ι) n) := by
  have hinj : Function.Injective
      (TauCeti.TateModule.levelMap (p := ℓ) (pointsToLocal E p hp ι) n) := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    rw [TauCeti.TateModule.levelMap_apply, TauCeti.TateModule.levelMap_apply] at h
    exact pointsToLocal_injective E p hp ι h
  have hℓQ : (ℓ : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hℓL : (ℓ : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hc1 : Nat.card (TauCeti.TateModuleLevel ℓ
      (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point n) = (ℓ ^ n) ^ 2 := by
    convert (E.baseChange (AlgebraicClosure ℚ)).natCard_tateModuleLevel hℓQ n
  have hc2 : Nat.card (TauCeti.TateModuleLevel ℓ
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point n) =
        (ℓ ^ n) ^ 2 := by
    convert ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).natCard_tateModuleLevel hℓL n
  have : Finite (TauCeti.TateModuleLevel ℓ
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point n) :=
    Nat.finite_of_card_ne_zero (by
      rw [hc2]
      exact pow_ne_zero 2 (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero))
  exact hinj.bijective_of_nat_card_le (by rw [hc1, hc2])

/-- **DEFINITION WITH PROVED BIJECTIVITY**, the isomorphism of Tate modules
`T_ℓ(E/\bar ℚ) ≅ T_ℓ(E/\bar ℚ_p)` induced by an embedding. Locators:
`levelMap_pointsToLocal_bijective`, `TateReduction.map_bijective_of_levelMap_bijective`. -/
def tateToLocal [E.IsElliptic]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime] :
    integralTate E ℓ ≃ₗ[ℤ_[ℓ]] TauCeti.TateModule ℓ
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point :=
  LinearEquiv.ofBijective (TauCeti.TateModule.mapLinearMap (pointsToLocal E p hp ι))
    (TateReduction.map_bijective_of_levelMap_bijective _
      (levelMap_pointsToLocal_bijective E p hp ι ℓ))

/-- **PROVED**, the isomorphism of Tate modules intertwines the global action through `r` with the
local action. Locators: `pointsToLocal_map`, Tau Ceti `TateModule.map_comp`. -/
theorem tateToLocal_equivariant [E.IsElliptic]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (r : LocalGaloisQ p hp →* GlueC10.GQ)
    (hres : ∀ (σ : LocalGaloisQ p hp) (x : AlgebraicClosure ℚ), ι (r σ x) = σ (ι x))
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : LocalGaloisQ p hp) (x : integralTate E ℓ) :
    tateToLocal E p hp ι ℓ (integralTateRep E ℓ (r σ) x) =
      (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ σ
        (tateToLocal E p hp ι ℓ x) := by
  have key : (pointsToLocal E p hp ι).comp (Affine.Point.map (W' := E) (r σ).toAlgHom) =
      (Affine.Point.map (W' := E.baseChange ((primeIdealQ p hp).adicCompletion ℚ))
        σ.toAlgHom).comp (pointsToLocal E p hp ι) :=
    AddMonoidHom.ext fun P => pointsToLocal_map E p hp ι r hres σ P
  change TauCeti.TateModule.map _ (TauCeti.TateModule.map _ x) =
    TauCeti.TateModule.map _ (TauCeti.TateModule.map _ x)
  rw [← AddMonoidHom.comp_apply (TauCeti.TateModule.map _), ← TauCeti.TateModule.map_comp, key,
    TauCeti.TateModule.map_comp, AddMonoidHom.comp_apply]

/-- **DEFINITION WITH PROVED INTERTWINING**, the isomorphism of the global rational Tate
representation, restricted along `r`, with the local rational Tate representation. Locators:
`tateToLocal_equivariant`, Mathlib `LinearEquiv.baseChange`. -/
def rationalTateToLocal [E.IsElliptic]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (r : LocalGaloisQ p hp →* GlueC10.GQ)
    (hres : ∀ (σ : LocalGaloisQ p hp) (x : AlgebraicClosure ℚ), ι (r σ x) = σ (ι x))
    (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation.Equiv ((rationalTateRep E ℓ).comp r)
      (Representation.baseChange ℚ_[ℓ]
        ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ)) :=
  { (tateToLocal E p hp ι ℓ).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ with
    isIntertwining' := fun σ => by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a m =>
        change (tateToLocal E p hp ι ℓ).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _
            ((integralTateRep E ℓ (r σ)).baseChange ℚ_[ℓ] (a ⊗ₜ m)) =
          (((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ
            σ).baseChange ℚ_[ℓ]) ((tateToLocal E p hp ι ℓ).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (a ⊗ₜ m))
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearMap.baseChange_tmul, tateToLocal_equivariant E p hp ι r hres ℓ σ m]
      | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add, h₁, h₂] }

/-- **PROVED FROM THE NAMED PRINT AND GLUE**, the multiplicative case of
`BadReductionTatePolynomialReadingCoinv`: at a prime `p ≠ ℓ` of multiplicative reduction the
corrected local Tate polynomial is the minimal-reduction polynomial, `1 - X` in the split case and
`1 + X` in the non-split case. The glue statement moves the global coinvariants and Frobenius to
the local ones through the Tate-module isomorphism `rationalTateToLocal` (base change of points
along `ι`); the print gives the Tate-curve shape there; `coinvariantEulerPolynomial_of_tateShape`
computes `1 - ε(Frob) X`; `localPolynomialQ_of_split` and `localPolynomialQ_of_nonsplit` give the
classical side. Locators: Silverman, Appendix C, Theorem C.14.1, read in `TateCurveTateModulePrint`;
`DecompositionGroupLocalGlobalGlue`. -/
theorem localTatePolynomialCoinv_of_multiplicative (hT : TateCurveTateModulePrint)
    (hLG : DecompositionGroupLocalGlobalGlue) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]
    (hpℓ : p ≠ ℓ)
    (hmult : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ))
    (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) := by
  obtain ⟨Γ, _, w, ι, r, hw, hres, hI, σF, hσF, hrσ⟩ := hLG p hp D
  obtain ⟨b, ε, χ, κ, h0, h1, hIε, hκ, hFε⟩ := hT E p hp ℓ hpℓ.symm hmult Γ w hw
  -- the local Frobenius normalizes the local inertia group
  have hσdec : σF ∈ w.valuationSubring.decompositionSubgroup
      ((primeIdealQ p hp).adicCompletion ℚ) := by
    have hσ' : ∀ x, w x ≤ 1 → w (σF x - x ^ p) < 1 := by
      intro x hx
      have h := hσF x hx
      rwa [primeIdealQ_absNorm] at h
    exact TateReduction.mem_decompositionSubgroup_of_frobenius w σF hp.ne_zero hσ'
  have hJ : ∀ j ∈ localInertia w, σF * j * σF⁻¹ ∈ localInertia w := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hj
    let g : w.valuationSubring.decompositionSubgroup ((primeIdealQ p hp).adicCompletion ℚ) :=
      ⟨σF, hσdec⟩
    have hn : (w.valuationSubring.inertiaSubgroup
        ((primeIdealQ p hp).adicCompletion ℚ)).Normal := by
      unfold ValuationSubring.inertiaSubgroup
      infer_instance
    exact Subgroup.mem_map.mpr ⟨g * s * g⁻¹, hn.conj_mem s hs g, rfl⟩
  -- step 1: the global coinvariants, read through the local group acting by `r`
  have step1 : localTatePolynomialCoinv E ℓ D =
      coinvariantEulerPolynomial ((rationalTateRep E ℓ).comp r) (localInertia w) σF hJ := by
    unfold localTatePolynomialCoinv
    refine coinvariantEulerPolynomial_congr _ _ _ _ _ _ _ _ ?_ ?_
    · rw [inertiaAugmentation_comp, hI]
    · rw [MonoidHom.comp_apply, hrσ]
  -- step 2: transport to the local Tate module
  let b' := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have : FiniteDimensional ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TauCeti.TateModule ℓ
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point)) :=
    Module.Finite.of_basis b'
  rw [step1, coinvariantEulerPolynomial_eq_of_equiv (rationalTateToLocal E p hp ι r hres ℓ) _ _ hJ]
  -- step 3: the Tate-curve shape of the local representation
  have hb'0 : b' 0 = 1 ⊗ₜ b 0 := Algebra.TensorProduct.basis_apply b 0
  have hb'1 : b' 1 = 1 ⊗ₜ b 1 := Algebra.TensorProduct.basis_apply b 1
  rw [coinvariantEulerPolynomial_of_tateShape _ _ _ hJ b'
      (fun σ => algebraMap ℤ_[ℓ] ℚ_[ℓ] (ε σ)) (fun σ => algebraMap ℤ_[ℓ] ℚ_[ℓ] (χ σ))
      (fun σ => algebraMap ℤ_[ℓ] ℚ_[ℓ] (κ σ)) ?_ ?_ ?_ ?_]
  · rw [hFε σF hσF]
    by_cases hs : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasSplitMultiplicativeReduction
          ((primeIdealQ p hp).adicCompletionIntegers ℚ)
    · simp only [hs, ↓reduceIte, localPolynomialQ_of_split E p hp hs]
      simp
    · simp only [hs, ↓reduceIte, localPolynomialQ_of_nonsplit E p hp hmult hs]
      simp
  · intro σ
    rw [hb'0, Representation.baseChange_apply, LinearMap.baseChange_tmul, h0 σ,
      TensorProduct.tmul_smul, ← map_mul, algebraMap_smul]
  · intro σ
    rw [hb'0, hb'1, Representation.baseChange_apply, LinearMap.baseChange_tmul, h1 σ,
      TensorProduct.tmul_smul, TensorProduct.tmul_add, TensorProduct.tmul_smul, algebraMap_smul,
      algebraMap_smul]
  · intro σ hσ
    obtain ⟨hε1, hχ1⟩ := hIε σ hσ
    exact ⟨by rw [hε1, map_one], by rw [hχ1, map_one]⟩
  · obtain ⟨σ, hσ, hκσ⟩ := hκ
    exact ⟨σ, hσ, (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])).mpr hκσ⟩

end Multiplicative

/-! ## Part G. The corrected bad-prime reading from its two cases -/

section Assembly

/-- **GLUE, STATED AND NOT PROVED: THE ADDITIVE CASE**, at a prime `p ≠ ℓ` of additive reduction
the inertia coinvariants of the actual rational Tate module vanish. By
`localTatePolynomialCoinv_of_additive` this is exactly what the additive case of
`BadReductionTatePolynomialReadingCoinv` needs. Classical route, with the manuscript-cited
locators (section-level, pages not checked): potential good reduction for integral `j` (Silverman
VII.5.5) with the criterion of Néron, Ogg and Shafarevich over the extension (VII.7.1) makes inertia
act through a finite group, nontrivially since the reduction is not good, with determinant the
cyclotomic character (III.8.1), so it has no fixed line and no coinvariants; for non-integral `j`
the curve is a ramified quadratic twist of a Tate curve (Appendix C, Theorem C.14.1). -/
def AdditiveReductionCoinvariantsVanish : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime),
    p ≠ ℓ → ¬GoodReductionAt E (primeIdealQ p hp) →
    ¬((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ) →
    ∀ D : LocalArithmeticFrobenius p,
      inertiaAugmentation (rationalTateRep E ℓ) (inertiaAt D) = ⊤

/-- **PROVED FROM THE NAMED INPUTS**, the corrected bad-prime reading: its multiplicative case from
the Tate-curve print and the local–global glue (`localTatePolynomialCoinv_of_multiplicative`), its
additive case from the vanishing of coinvariants (`localTatePolynomialCoinv_of_additive`). -/
theorem badReductionTatePolynomialReadingCoinv_of_inputs (hT : TateCurveTateModulePrint)
    (hLG : DecompositionGroupLocalGlobalGlue) (hA : AdditiveReductionCoinvariantsVanish) :
    BadReductionTatePolynomialReadingCoinv := by
  intro E _ ℓ _ p hp hpℓ hgood D
  by_cases hmult : ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).minimal
      ((primeIdealQ p hp).adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)
  · exact localTatePolynomialCoinv_of_multiplicative E p hp hT hLG ℓ hpℓ hmult D
  · exact localTatePolynomialCoinv_of_additive E ℓ p hp hgood hmult D
      (hA E ℓ p hp hpℓ hgood hmult D)

end Assembly

/-! ## Part H. Coinvariants and Carayol's cohomological normalization -/

section Dual

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- **PROVED**, the inertia-invariant functionals are the annihilator of the augmentation
subspace. Locators: Mathlib `Representation.dual_apply`, `Submodule.mem_dualAnnihilator`. -/
theorem fixedInertia_dual_eq (ρ : Representation K G V) (I : Subgroup G) :
    fixedInertia ρ.dual I = (inertiaAugmentation ρ I).dualAnnihilator := by
  ext φ
  rw [Submodule.mem_dualAnnihilator]
  change (∀ i : I, ρ.dual (i : G) φ = φ) ↔ _
  constructor
  · intro h w hw
    have hle : inertiaAugmentation ρ I ≤ LinearMap.ker φ := by
      rw [inertiaAugmentation, Submodule.span_le]
      rintro _ ⟨i, hi, v, rfl⟩
      have hv := congrArg (fun ψ : Module.Dual K V => ψ v) (h ⟨i⁻¹, inv_mem hi⟩)
      simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
        inv_inv] at hv
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hv, sub_self]
    exact hle hw
  · intro h i
    apply LinearMap.ext
    intro v
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    have hmem : ρ (i : G)⁻¹ v - v ∈ inertiaAugmentation ρ I :=
      Submodule.subset_span ⟨(i : G)⁻¹, inv_mem i.2, v, rfl⟩
    have := h _ hmem
    rwa [map_sub, sub_eq_zero] at this

/-- **PROVED**, a transpose has the same characteristic polynomial. Locators: Mathlib
`LinearMap.toMatrix_transpose`, `Matrix.charpoly_transpose`. -/
theorem charpoly_dual_transpose {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : Module.End K W) :
    LinearMap.charpoly (Module.Dual.transpose (R := K) f) = LinearMap.charpoly f := by
  let b := Module.finBasis K W
  rw [← LinearMap.charpoly_toMatrix (Module.Dual.transpose (R := K) f) b.dualBasis,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose, LinearMap.charpoly_toMatrix]

/-- **PROVED**, the coinvariant polynomial with `g` is the invariant polynomial of the dual
representation with `g⁻¹`: arithmetic Frobenius on the coinvariants of the homological
normalization is geometric Frobenius on the invariants of the cohomological one. The dual of `V_I`
is the subspace of invariant functionals (`fixedInertia_dual_eq`, Mathlib
`Submodule.dualQuotEquivDualAnnihilator`), on which `ρ^*(g⁻¹)` is the transpose of the action of `g`
on `V_I`. -/
theorem coinvariantEulerPolynomial_eq_dual [FiniteDimensional K V] (ρ : Representation K G V)
    (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g * i * g⁻¹ ∈ I)
    (hg' : ∀ i ∈ I, (g⁻¹)⁻¹ * i * g⁻¹ ∈ I) :
    coinvariantEulerPolynomial ρ I g hg = inertiaEulerPolynomial ρ.dual I g⁻¹ hg' := by
  let e : Module.Dual K (inertiaCoinvariants ρ I) ≃ₗ[K] fixedInertia ρ.dual I :=
    (inertiaAugmentation ρ I).dualQuotEquivDualAnnihilator.trans
      (LinearEquiv.ofEq _ _ (fixedInertia_dual_eq ρ I).symm)
  have hc : e.conj (Module.Dual.transpose (R := K) (coinvariantFrobenius ρ I g hg)) =
      inertiaFrobenius ρ.dual I g⁻¹ hg' := by
    apply LinearMap.ext
    intro θ
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    change (inertiaAugmentation ρ I).dualQuotEquivDualAnnihilator
        (Module.Dual.transpose (R := K) (coinvariantFrobenius ρ I g hg) (e.symm θ)) v =
      (ρ.dual g⁻¹ (θ : Module.Dual K V)) v
    rw [Submodule.dualQuotEquivDualAnnihilator_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, coinvariantFrobenius_mk, Representation.dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv]
    change (inertiaAugmentation ρ I).dualQuotEquivDualAnnihilator.symm
        ((LinearEquiv.ofEq _ _ (fixedInertia_dual_eq ρ I).symm).symm θ)
          (Submodule.Quotient.mk (ρ g v)) = _
    rw [Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk]
    rfl
  have : Module.Free K (fixedInertia ρ.dual I) := Module.Free.of_equiv e
  unfold inertiaEulerPolynomial coinvariantEulerPolynomial
  rw [← hc, LinearEquiv.charpoly_conj, charpoly_dual_transpose]

end Dual

/-- **PROVED**, the corrected local Tate polynomial is the geometric-Frobenius polynomial on the
inertia invariants of the dual of the actual rational Tate module. Locator:
`coinvariantEulerPolynomial_eq_dual`. -/
theorem localTatePolynomialCoinv_eq_dual (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
    [Fact ℓ.Prime] {p : ℕ} (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D =
      inertiaEulerPolynomial (rationalTateRep E ℓ).dual (inertiaAt D) D.element⁻¹
        (fun i hi => by simpa only [inv_inv] using inertiaAt_conj D i hi) :=
  coinvariantEulerPolynomial_eq_dual _ _ _ _ _

/-- **PROVED**, the corrected local-factor field is literally Carayol's cohomological
normalization: the geometric Frobenius `D.element⁻¹` on the inertia invariants of
`CarayolRationalRealizationCoinv.cohomologicalRep`, the dual of the normalized representation
(Carayol 1986, §§0.4–0.8, pp. 409–411). The excluded invariant-space realization is archived in
`docs/research/g0-representation-route-invariants.md`. Locator:
`coinvariantEulerPolynomial_eq_dual`. -/
theorem CarayolRationalRealizationCoinv.local_factor_cohomological {M : ℕ} [NeZero M]
    {F : Newform M 2} {hχ : F.χ = 1} {b : ℕ → ℚ}
    {hb : ∀ n : ℕ, (qExpansion 1 F.toCuspForm).coeff n = (b n : ℂ)} {ℓ : ℕ} [Fact ℓ.Prime]
    (R : CarayolRationalRealizationCoinv F hχ b hb ℓ) (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (D : LocalArithmeticFrobenius p) :
    inertiaEulerPolynomial R.normalizedRep.dual (inertiaAt D) D.element⁻¹
        (fun i hi => by simpa only [inv_inv] using inertiaAt_conj D i hi) =
      rationalNewformPolynomial M ℓ b p := by
  rw [← coinvariantEulerPolynomial_eq_dual]
  exact R.local_factor p hp hpℓ D

end ZInQ.Contrib.RC53Assist.GlobalTrace
