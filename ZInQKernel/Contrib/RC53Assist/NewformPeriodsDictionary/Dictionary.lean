import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Data.Fintype.Option
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Reduction
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MapsInfinity
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois

/-!
# Reading translations for newform periods

The Euler polynomial is computed on the reduction of a minimal Weierstrass equation.
The point count includes the point at infinity. All identities concern the existing
Weierstrass curves, arithmetic functions, and Hecke actions.

References: Silverman, The Arithmetic of Elliptic Curves, V.2 and VII.5;
Shimura, On the factors of the jacobian variety of a modular function field,
Theorem 1, pp. 525–526; Faltings, Endlichkeitssätze für abelsche Varietäten
über Zahlkörpern, §5, Korollar 2, p. 361.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

open Polynomial ArithmeticFunction NumberField IsDedekindDomain

section Local

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (E : WeierstrassCurve K)

/-- The integer trace obtained by counting points on the minimal reduction. -/
def reductionTrace : ℤ :=
  (Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
    (Nat.card ((E.minimal R).reduction R).toAffine.Point : ℤ)

/-- At good reduction the existing local polynomial is the usual quadratic. -/
theorem localPolynomial_eq_of_good
    (h : WeierstrassCurve.HasGoodReduction R (E.minimal R)) :
    E.localPolynomial R =
      1 - C (reductionTrace R E) * X +
        C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  classical
  simp [WeierstrassCurve.localPolynomial, h, reductionTrace]

/-- Every local polynomial has constant coefficient one, including at bad reduction. -/
theorem localPolynomial_coeff_zero : (E.localPolynomial R).coeff 0 = 1 := by
  classical
  unfold WeierstrassCurve.localPolynomial
  split_ifs <;> simp

/-- Every local reciprocal series has constant coefficient one. -/
theorem localPowerSeries_constantCoeff : (E.localPowerSeries R).constantCoeff = 1 := by
  simp [WeierstrassCurve.localPowerSeries]

/-- The first coefficient of the reciprocal of a unit-constant series is its negative linear coefficient. -/
theorem invOfUnit_coeff_one (f : PowerSeries ℤ) :
    (PowerSeries.invOfUnit f 1).coeff 1 = -f.coeff 1 := by
  have h₀ : (PowerSeries.invOfUnit f 1).coeff 0 = 1 := by
    simp
  rw [PowerSeries.coeff_invOfUnit]
  simp [show Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} by decide, h₀]

/-- The first local reciprocal coefficient at good reduction is the point-count trace. -/
theorem localPowerSeries_coeff_one_of_good
    (h : WeierstrassCurve.HasGoodReduction R (E.minimal R)) :
    (E.localPowerSeries R).coeff 1 = reductionTrace R E := by
  rw [WeierstrassCurve.localPowerSeries, invOfUnit_coeff_one, Polynomial.coeff_coe,
    localPolynomial_eq_of_good R E h]
  simp [Polynomial.coeff_one]

/-- Evaluating the local arithmetic function at the residue cardinality reads its linear coefficient. -/
theorem localEulerFactor_at_residue_card_of_good
    (hq : 1 < Nat.card (IsLocalRing.ResidueField R))
    (h : WeierstrassCurve.HasGoodReduction R (E.minimal R)) :
    E.localEulerFactor R (Nat.card (IsLocalRing.ResidueField R)) = reductionTrace R E := by
  simpa only [WeierstrassCurve.localEulerFactor, pow_one] using
    (ArithmeticFunction.ofPowerSeries_apply_pow hq (E.localPowerSeries R) 1).trans
      (localPowerSeries_coeff_one_of_good R E h)

/-- The good local factor, with its variable left unevaluated, is the reciprocal of the point-count polynomial. -/
theorem localPowerSeries_eq_of_good
    (h : WeierstrassCurve.HasGoodReduction R (E.minimal R)) :
    E.localPowerSeries R = PowerSeries.invOfUnit
      ((1 - C (reductionTrace R E) * X +
        C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1 := by
  rw [WeierstrassCurve.localPowerSeries, localPolynomial_eq_of_good R E h]

end Local

section ResidueFields

open IsDedekindDomain.HeightOneSpectrum
open scoped Topology WithZero

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  (v : HeightOneSpectrum A)

/-- Reduction of a global integer in the residue field of its completion. -/
def residueMapCompletion : A →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
    (algebraMap A (v.adicCompletionIntegers K))

/-- The maximal ideal in the completed integer ring is the open unit ball. -/
theorem mem_maximalIdeal_completion_iff (z : v.adicCompletionIntegers K) :
    z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) z.1 < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  exact ne_iff_lt_iff_le.mpr z.2

/-- The completed residue map has precisely the original prime ideal as kernel. -/
theorem ker_residueMapCompletion : RingHom.ker (residueMapCompletion (K := K) v) = v.asIdeal := by
  ext r
  simp only [RingHom.mem_ker, residueMapCompletion, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_completion_iff]
  rw [algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation' v ((algebraMap A K) r),
    valuation_lt_one_iff_mem]

/-- Completion does not introduce new residue classes. -/
theorem residueMapCompletion_surjective :
    Function.Surjective (residueMapCompletion (K := K) v) := by
  intro y
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  have hnbhd : {t : v.adicCompletion K |
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict (t - (z : v.adicCompletion K)) < 1}
      ∈ 𝓝 (z : v.adicCompletion K) :=
    Valued.mem_nhds.mpr ⟨1, fun _ h => h⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap K v).mem_nhds hnbhd
  have hkclose : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (algebraMap K (v.adicCompletion K) k - (z : v.adicCompletion K)) < 1 :=
    (Valuation.restrict_lt_one_iff _).mp hk
  have hkint : (v.valuation K) k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' v k]
    change Valued.v (algebraMap K (v.adicCompletion K) k) ≤ 1
    have htri := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_add
      (algebraMap K (v.adicCompletion K) k - (z : v.adicCompletion K)) (z : v.adicCompletion K)
    rw [sub_add_cancel] at htri
    exact htri.trans (max_le hkclose.le z.2)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer v hkint 1
  refine ⟨r, ?_⟩
  apply sub_eq_zero.mp
  change (IsLocalRing.residue (v.adicCompletionIntegers K))
    (algebraMap A (v.adicCompletionIntegers K) r) -
      (IsLocalRing.residue (v.adicCompletionIntegers K)) z = 0
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_completion_iff]
  change Valued.v (algebraMap A (v.adicCompletion K) r - (z : v.adicCompletion K)) < 1
  have hr' : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (algebraMap A (v.adicCompletion K) r - algebraMap K (v.adicCompletion K) k) < 1 := by
    rw [IsScalarTower.algebraMap_apply A K (v.adicCompletion K), ← map_sub]
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (((algebraMap A K) r - k : K) : v.adicCompletion K) < 1
    rw [valuedAdicCompletion_eq_valuation' v]
    exact hr
  have htri := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_add
    (algebraMap A (v.adicCompletion K) r - algebraMap K (v.adicCompletion K) k)
    (algebraMap K (v.adicCompletion K) k - (z : v.adicCompletion K))
  rw [sub_add_sub_cancel] at htri
  exact htri.trans_lt (max_lt hr' hkclose)

/-- The original residue field and the residue field of the completion are isomorphic. -/
def residueFieldEquivCompletion :
    (A ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_residueMapCompletion (K := K) v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residueMapCompletion_surjective (K := K) v))

/-- The residue cardinality used in the existing local Euler factor is the prime-ideal norm. -/
theorem card_residueField_completion [Infinite A] :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = v.asIdeal.absNorm := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (residueFieldEquivCompletion (K := K) v).symm.toEquiv

end ResidueFields

section RationalPrimes

/-- The norm is unchanged by identifying the rational integers with the integers. -/
theorem absNorm_map_rational_integers (I : Ideal (𝓞 ℚ)) :
    (I.map Rat.ringOfIntegersEquiv).absNorm = I.absNorm := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I (I.map Rat.ringOfIntegersEquiv) Rat.ringOfIntegersEquiv rfl).symm.toEquiv

/-- A nonzero prime ideal over the rationals has prime norm. -/
theorem prime_absNorm_rational (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal.absNorm.Prime := by
  let J := v.asIdeal.map Rat.ringOfIntegersEquiv
  have : v.asIdeal.IsPrime := v.isPrime
  have : J.IsPrime := Ideal.map_isPrime_of_equiv Rat.ringOfIntegersEquiv
  have hJ : J ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective Rat.ringOfIntegersEquiv.injective).not.mpr v.ne_bot
  rw [← absNorm_map_rational_integers v.asIdeal]
  exact (Int.prime_absNorm J).mpr (Ideal.prime_of_isPrime hJ inferInstance)

/-- A rational prime ideal is uniquely determined by its norm. -/
theorem absNorm_rational_injective :
    Function.Injective (fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal.absNorm) := by
  intro v w h
  have h' : (v.asIdeal.map Rat.ringOfIntegersEquiv).absNorm =
      (w.asIdeal.map Rat.ringOfIntegersEquiv).absNorm := by
    rw [absNorm_map_rational_integers, absNorm_map_rational_integers]
    exact h
  have h'' := congrArg (fun n : ℕ => Ideal.span {(n : ℤ)}) h'
  simp only [Int.ideal_span_absNorm_eq_self] at h''
  apply HeightOneSpectrum.ext
  apply Ideal.comap_injective_of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective
  have hv : v.asIdeal.map Rat.ringOfIntegersEquiv =
      v.asIdeal.comap Rat.ringOfIntegersEquiv.symm :=
    Ideal.map_comap_of_equiv Rat.ringOfIntegersEquiv
  have hw : w.asIdeal.map Rat.ringOfIntegersEquiv =
      w.asIdeal.comap Rat.ringOfIntegersEquiv.symm :=
    Ideal.map_comap_of_equiv Rat.ringOfIntegersEquiv
  exact hv.symm.trans (h''.trans hw)

/-- The ideal generated by a natural number over the rationals has that norm. -/
theorem absNorm_span_rational (n : ℕ) :
    (Ideal.span {(n : 𝓞 ℚ)}).absNorm = n := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  simp

/-- The prime ideal over a specified rational prime. -/
def primeIdealQ (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(p : 𝓞 ℚ)}
  isPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [absNorm_span_rational]
    exact (Nat.irreducible_iff_nat_prime p).mpr hp)
  ne_bot := by
    intro h
    have hn := absNorm_span_rational p
    rw [h, Ideal.absNorm_bot] at hn
    exact hp.ne_zero hn.symm

/-- The specified prime ideal has the specified norm. -/
theorem primeIdealQ_absNorm (p : ℕ) (hp : p.Prime) : (primeIdealQ p hp).asIdeal.absNorm = p :=
  absNorm_span_rational p

/-- The residue field in the rational completion has exactly `p` elements. -/
theorem card_residueField_primeIdealQ (p : ℕ) (hp : p.Prime) :
    Nat.card (IsLocalRing.ResidueField ((primeIdealQ p hp).adicCompletionIntegers ℚ)) = p := by
  rw [card_residueField_completion, primeIdealQ_absNorm]

/-- There are only finitely many prime ideals with bounded completed residue cardinality. -/
theorem residueCard_northcott (K : Type*) [Field K] [NumberField K] :
    Northcott (fun v : HeightOneSpectrum (𝓞 K) =>
      Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) := by
  constructor
  intro B
  simpa only [card_residueField_completion] using
    (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 K) B)

end RationalPrimes

section EulerProducts

variable {ι B : Type*} [CommSemiring B]

/-- Dirichlet convolution at a prime has only its two possible factorizations. -/
theorem convolution_at_prime (f g : ArithmeticFunction B) {p : ℕ} (hp : p.Prime) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  classical
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), hp.divisors,
    Finset.sum_insert (show 1 ∉ ({p} : Finset ℕ) by
      simp only [Finset.mem_singleton]
      exact hp.ne_one.symm),
    Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos]

/-- The first coefficient of a finite product of normalized local factors is one. -/
theorem finsetProduct_at_one (s : Finset ι) (f : ι → ArithmeticFunction B)
    (hf : ∀ i, f i 1 = 1) : (∏ i ∈ s, f i) 1 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, ArithmeticFunction.mul_apply_one, hf i, ih, one_mul]

/-- A prime coefficient in a product of normalized local factors is their sum. -/
theorem finsetProduct_at_prime (s : Finset ι) (f : ι → ArithmeticFunction B)
    (hf : ∀ i, f i 1 = 1) {p : ℕ} (hp : p.Prime) :
    (∏ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp.ne_one]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, convolution_at_prime _ _ hp, hf i,
        finsetProduct_at_one s f hf, ih, Finset.sum_insert hi]
      simp [add_comm]

/-- A local series supported on powers of one base contributes nothing at a different prime. -/
theorem ofPowerSeries_at_other_prime {p q : ℕ} (hp : p.Prime) (hq : 1 < q)
    (hne : q ≠ p) (f : PowerSeries B) : ArithmeticFunction.ofPowerSeries q f p = 0 := by
  classical
  rw [ArithmeticFunction.ofPowerSeries_apply hq, Function.extend_apply', Pi.zero_apply]
  rintro ⟨k, hk⟩
  cases k with
  | zero => exact hp.ne_one (by simpa using hk.symm)
  | succ k =>
      have hqp : q ∣ p := ⟨q ^ k, hk.symm.trans (pow_succ' q k)⟩
      exact hne ((hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.ne')

/-- A normalized Euler product with distinct prime bases has the expected coefficient at each prime. -/
theorem eulerProduct_coeff_at_prime (q : ι → ℕ) [Northcott q]
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (f : ι → PowerSeries B) (hf : ∀ i, (f i).constantCoeff = 1) (i : ι) :
    ArithmeticFunction.eulerProduct (fun j => ArithmeticFunction.ofPowerSeries (q j) (f j))
        (q i) = (f i).coeff 1 := by
  classical
  have hn : ∀ j, ArithmeticFunction.ofPowerSeries (q j) (f j) 1 = 1 := by
    intro j
    rw [ArithmeticFunction.ofPowerSeries_apply_one, hf j]
  have hpartial : ∀ s : Finset ι, i ∈ s →
      (∏ j ∈ s, ArithmeticFunction.ofPowerSeries (q j) (f j)) (q i) = (f i).coeff 1 := by
    intro s his
    rw [finsetProduct_at_prime s _ hn (hq i)]
    calc
      (∑ j ∈ s, ArithmeticFunction.ofPowerSeries (q j) (f j) (q i)) =
          ArithmeticFunction.ofPowerSeries (q i) (f i) (q i) := by
        refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => (h his).elim)
        exact ofPowerSeries_at_other_prime (hq i) (hq j).one_lt
          (fun h => hji (hinj h)) (f j)
      _ = (f i).coeff 1 := by
        simpa only [pow_one] using
          ArithmeticFunction.ofPowerSeries_apply_pow (hq i).one_lt (f i) 1
  have he := ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries q f hf (q i)
  have hi : ∀ᶠ s : Finset ι in Filter.atTop, i ∈ s :=
    Filter.eventually_atTop.mpr ⟨{i}, fun s hs => hs (Finset.mem_singleton_self i)⟩
  obtain ⟨s, hs, his⟩ := (he.and hi).exists
  exact hs.symm.trans (hpartial s his)

end EulerProducts

section RationalEulerFactors

/-- The minimal reduction at a rational prime ideal, over its actual residue field. -/
def reducedCurveQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    WeierstrassCurve (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
  ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
    (v.adicCompletionIntegers ℚ)

/-- Good reduction is tested on the minimal equation used by the existing local factor. -/
def GoodReductionAt (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  WeierstrassCurve.HasGoodReduction (v.adicCompletionIntegers ℚ)
    ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ))

/-- The completed residue field at `p` is the prime field with `p` elements. -/
def residueFieldEquivZModQ (p : ℕ) (hp : p.Prime) :
    IsLocalRing.ResidueField ((primeIdealQ p hp).adicCompletionIntegers ℚ) ≃+* ZMod p :=
  (residueFieldEquivCompletion (K := ℚ) (primeIdealQ p hp)).symm.trans
    ((Ideal.quotientEquiv (primeIdealQ p hp).asIdeal (Ideal.span {(p : ℤ)})
      Rat.ringOfIntegersEquiv (by
        dsimp only [primeIdealQ]
        rw [Ideal.map_span]
        simp)).trans (Int.quotientSpanNatEquivZMod p))

/-- A coefficient-field isomorphism identifies the nonsingular points, including infinity. -/
def affinePointEquivOfRingEquiv {F K : Type*} [Field F] [Field K]
    (W : WeierstrassCurve.Affine F) (e : F ≃+* K) :
    W.Point ≃ (W.map e.toRingHom).Point :=
  W.nonsingularPointEquiv.trans
    (((Equiv.subtypeEquiv (Equiv.prodCongr e.toEquiv e.toEquiv)
      (fun xy => (W.map_nonsingular e.injective xy.1 xy.2).symm)).optionCongr).trans
        (W.map e.toRingHom).nonsingularPointEquiv.symm)

/-- Point counts are preserved by coefficient-field isomorphisms. -/
theorem card_affinePoint_map {F K : Type*} [Field F] [Field K]
    (W : WeierstrassCurve.Affine F) (e : F ≃+* K) :
    Nat.card (W.map e.toRingHom).Point = Nat.card W.Point :=
  Nat.card_congr (affinePointEquivOfRingEquiv W e).symm

/-- The minimal reduction regarded as a genuine Weierstrass curve over the prime field. -/
def reducedCurveModP (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) : WeierstrassCurve (ZMod p) :=
  (reducedCurveQ E (primeIdealQ p hp)).map (residueFieldEquivZModQ p hp).toRingHom

/-- The prime-field model and the actual completed-residue model have the same point count. -/
theorem card_reducedCurveModP (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) :
    Nat.card (reducedCurveModP E p hp).toAffine.Point =
      Nat.card (reducedCurveQ E (primeIdealQ p hp)).toAffine.Point := by
  have : Fact p.Prime := ⟨hp⟩
  exact card_affinePoint_map (reducedCurveQ E (primeIdealQ p hp)).toAffine
    (residueFieldEquivZModQ p hp)

/-- The completed-residue point count is finite, so the natural cardinality is not a junk value. -/
theorem finite_reducedCurveQ_points (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Finite (reducedCurveQ E v).toAffine.Point := by
  classical
  have hk : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) ≠ 0 := by
    rw [card_residueField_completion]
    exact (prime_absNorm_rational v).ne_zero
  have hfin : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Nat.finite_of_card_ne_zero hk
  let : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := Fintype.ofFinite _
  exact Finite.of_equiv
    (Option {xy : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) ×
      IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) //
        (reducedCurveQ E v).toAffine.Nonsingular xy.1 xy.2})
    (reducedCurveQ E v).toAffine.nonsingularPointEquiv.symm

/-- The points counted over the prime field are finite, with infinity included. -/
theorem finite_reducedCurveModP_points (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) :
    Finite (reducedCurveModP E p hp).toAffine.Point := by
  classical
  have hp' : Fact p.Prime := ⟨hp⟩
  exact Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // (reducedCurveModP E p hp).toAffine.Nonsingular xy.1 xy.2})
    (reducedCurveModP E p hp).toAffine.nonsingularPointEquiv.symm

/-- A good minimal reduction is elliptic, so its nonsingular points are all its curve points. -/
theorem reducedCurveQ_isElliptic (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h : GoodReductionAt E v) : (reducedCurveQ E v).IsElliptic :=
  (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
    (v.adicCompletionIntegers ℚ)).mp h

/-- The prime-field reduction of a good curve is elliptic. -/
theorem reducedCurveModP_isElliptic (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (h : GoodReductionAt E (primeIdealQ p hp)) : (reducedCurveModP E p hp).IsElliptic := by
  have hE : (reducedCurveQ E (primeIdealQ p hp)).IsElliptic :=
    reducedCurveQ_isElliptic E (primeIdealQ p hp) h
  dsimp only [reducedCurveModP]
  infer_instance

/-- The prime coefficient of the global series equals the linear coefficient of its local reciprocal series. -/
theorem lFunction_at_primeIdeal (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    E.LFunction v.asIdeal.absNorm =
      ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)).coeff 1 := by
  let q := fun w : HeightOneSpectrum (𝓞 ℚ) =>
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ))
  let f := fun w : HeightOneSpectrum (𝓞 ℚ) =>
    (E.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ)
  have hq : ∀ w, (q w).Prime := by
    intro w
    simpa only [q, card_residueField_completion] using prime_absNorm_rational w
  have hinj : Function.Injective q := by
    intro w u h
    apply absNorm_rational_injective
    simpa only [q, card_residueField_completion] using h
  have : Northcott q := residueCard_northcott ℚ
  have hf : ∀ w, (f w).constantCoeff = 1 := by
    intro w
    exact localPowerSeries_constantCoeff _ _
  have h := eulerProduct_coeff_at_prime q hq hinj f hf v
  have hL : E.LFunction =
      ArithmeticFunction.eulerProduct
        (fun w => ArithmeticFunction.ofPowerSeries (q w) (f w)) := by
    unfold WeierstrassCurve.LFunction
    apply congrArg ArithmeticFunction.eulerProduct
    funext w
    dsimp only [q, f, WeierstrassCurve.localEulerFactor]
    apply congrArg (ArithmeticFunction.ofPowerSeries
      (Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ))))
    apply congrArg (fun W : WeierstrassCurve (w.adicCompletion ℚ) =>
      W.localPowerSeries (w.adicCompletionIntegers ℚ))
    unfold WeierstrassCurve.baseChange
    apply congrArg (WeierstrassCurve.map E)
    exact Subsingleton.elim _ _
  rw [hL]
  simpa only [q, f, card_residueField_completion] using h

/-- The global coefficient at a good prime ideal is the point-count trace. -/
theorem lFunction_at_primeIdeal_of_good (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : GoodReductionAt E v) :
    E.LFunction v.asIdeal.absNorm = (v.asIdeal.absNorm : ℤ) + 1 -
      (Nat.card (reducedCurveQ E v).toAffine.Point : ℤ) := by
  rw [lFunction_at_primeIdeal,
    localPowerSeries_coeff_one_of_good (v.adicCompletionIntegers ℚ)
      (E.baseChange (v.adicCompletion ℚ)) h]
  simp only [reductionTrace, reducedCurveQ, card_residueField_completion]

/-- The existing global coefficient at `p` is `p + 1` minus the number of points of the good reduction. -/
theorem lFunction_prime_eq_pointCount (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (h : GoodReductionAt E (primeIdealQ p hp)) :
    E.LFunction p = (p : ℤ) + 1 -
      (Nat.card (reducedCurveQ E (primeIdealQ p hp)).toAffine.Point : ℤ) := by
  simpa only [primeIdealQ_absNorm] using lFunction_at_primeIdeal_of_good E (primeIdealQ p hp) h

/-- The requested prime-field point-count identity, with the point at infinity included. -/
theorem lFunction_prime_eq_card_ZMod (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (h : GoodReductionAt E (primeIdealQ p hp)) :
    E.LFunction p = (p : ℤ) + 1 - (Nat.card (reducedCurveModP E p hp).toAffine.Point : ℤ) := by
  rw [card_reducedCurveModP]
  exact lFunction_prime_eq_pointCount E p hp h

/-- The existing local Euler polynomial, indexed by a rational prime ideal. -/
def localPolynomialQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℤ[X] :=
  (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ)

/-- The good Euler polynomial has the actual global Dirichlet coefficient as its trace coefficient. -/
theorem localPolynomialQ_eq_of_good (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : GoodReductionAt E v) :
    localPolynomialQ E v = 1 - C (E.LFunction v.asIdeal.absNorm) * X +
      C (v.asIdeal.absNorm : ℤ) * X ^ 2 := by
  have ht : reductionTrace (v.adicCompletionIntegers ℚ) (E.baseChange (v.adicCompletion ℚ)) =
      E.LFunction v.asIdeal.absNorm :=
    ((lFunction_at_primeIdeal E v).trans
      (localPowerSeries_coeff_one_of_good (v.adicCompletionIntegers ℚ)
        (E.baseChange (v.adicCompletion ℚ)) h)).symm
  rw [localPolynomialQ, localPolynomial_eq_of_good _ _ h, ht, card_residueField_completion]

/-- At good reduction a local polynomial agrees exactly when its prime trace coefficient agrees. -/
theorem localPolynomialQ_eq_iff (E₁ E₂ : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h₁ : GoodReductionAt E₁ v) (h₂ : GoodReductionAt E₂ v) :
    localPolynomialQ E₁ v = localPolynomialQ E₂ v ↔
      E₁.LFunction v.asIdeal.absNorm = E₂.LFunction v.asIdeal.absNorm := by
  rw [localPolynomialQ_eq_of_good E₁ v h₁, localPolynomialQ_eq_of_good E₂ v h₂]
  constructor
  · intro h
    have hc := congrArg (fun P : ℤ[X] => P.coeff 1) h
    simpa [Polynomial.coeff_one] using hc
  · intro h
    rw [h]

/-- The rational function obtained by evaluating the existing local polynomial and taking its reciprocal. -/
def localFactorValueQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (T : ℂ) : ℂ :=
  ((localPolynomialQ E v).eval₂ (Int.castRingHom ℂ) T)⁻¹

/-- Evaluation gives the standard good-prime rational Euler factor. -/
theorem localFactorValueQ_eq_of_good (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h : GoodReductionAt E v) (T : ℂ) :
    localFactorValueQ E v T =
      (1 - (E.LFunction v.asIdeal.absNorm : ℂ) * T + (v.asIdeal.absNorm : ℂ) * T ^ 2)⁻¹ := by
  rw [localFactorValueQ, localPolynomialQ_eq_of_good E v h]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_one]
  rfl

/-- Equal good-prime coefficients imply equality of all existing local power series and local arithmetic factors. -/
theorem localFactors_eq_of_coeff_eq (E₁ E₂ : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (h₁ : GoodReductionAt E₁ v) (h₂ : GoodReductionAt E₂ v)
    (h : E₁.LFunction v.asIdeal.absNorm = E₂.LFunction v.asIdeal.absNorm) :
    (E₁.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ) =
        (E₂.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ) ∧
      (E₁.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ) =
        (E₂.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ) ∧
      ∀ T : ℂ, localFactorValueQ E₁ v T = localFactorValueQ E₂ v T := by
  have hP := (localPolynomialQ_eq_iff E₁ E₂ v h₁ h₂).mpr h
  have hS : (E₁.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ) =
      (E₂.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ) := by
    unfold WeierstrassCurve.localPowerSeries
    exact congrArg (fun P : ℤ[X] => PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) hP
  refine ⟨hS, ?_, fun T => ?_⟩
  · rw [WeierstrassCurve.localEulerFactor, WeierstrassCurve.localEulerFactor, hS]
  · rw [localFactorValueQ, localFactorValueQ, hP]

end RationalEulerFactors

section GoodReduction

open WeierstrassCurve IsDedekindDomain.HeightOneSpectrum Filter
open scoped WithZero

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve K) [WeierstrassCurve.IsIntegral R W]

/-- A unit integral discriminant has valuation one. -/
theorem valuation_Δ_eq_one_of_integralModel_isUnit
    (hΔ : IsUnit (integralModel R W).Δ) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) W.Δ = 1 := by
  rw [← integralModel_Δ_eq R W, valuation_eq_one_iff_notMem]
  intro hmem
  exact (IsDiscreteValuationRing.maximalIdeal R).isPrime.ne_top
    ((IsDiscreteValuationRing.maximalIdeal R).asIdeal.eq_top_of_isUnit_mem hmem hΔ)

/-- Any minimal equation of a curve with a unit integral discriminant has good reduction. -/
theorem hasGoodReduction_minimal_of_integral_unit_Δ
    (hΔ : IsUnit (integralModel R W).Δ) : HasGoodReduction R (W.minimal R) := by
  have hval := valuation_Δ_eq_one_of_integralModel_isUnit R W hΔ
  let C := (W.exists_isMinimal R).choose
  have hC : C⁻¹ • W.minimal R = W := by
    simp [WeierstrassCurve.minimal, C, smul_smul]
  have hInt : WeierstrassCurve.IsIntegral R (C⁻¹ • W.minimal R) := hC.symm ▸ inferInstance
  have hmax := (IsMinimal.val_Δ_maximal (R := R) (W := W.minimal R)).le hInt
  simp only [hC, one_smul] at hmax
  constructor
  have hlow : 1 ≤ valuation K (IsDiscreteValuationRing.maximalIdeal R) (W.minimal R).Δ := by
    calc
      1 = (valuation_Δ_aux R W : ℤᵐ⁰) := by
        rw [valuation_Δ_aux_eq_of_isIntegral, hval]
      _ ≤ (valuation_Δ_aux R (W.minimal R) : ℤᵐ⁰) := hmax
      _ = valuation K (IsDiscreteValuationRing.maximalIdeal R) (W.minimal R).Δ :=
        valuation_Δ_aux_eq_of_isIntegral R (W.minimal R)
  have hu : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W.minimal R).Δ ≤ 1 := by
    rw [← valuation_Δ_aux_eq_of_isIntegral R (W.minimal R)]
    exact (valuation_Δ_aux R (W.minimal R)).2
  exact le_antisymm hu hlow

end GoodReduction

section AlmostAllPrimes

open WeierstrassCurve IsDedekindDomain.HeightOneSpectrum Filter
open scoped WithZero

/-- The canonical rational embedding into a completion preserves the valuation. -/
theorem valued_algebraMap_Q (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℚ) :
    (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰) (algebraMap ℚ (v.adicCompletion ℚ) x) =
      (v.valuation ℚ) x := by
  have hm : algebraMap ℚ (v.adicCompletion ℚ) = NumberField.FinitePlace.embedding v :=
    RingHom.ext_rat _ _
  rw [hm, NumberField.FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation' v]

/-- Integral rational coefficients give an integral equation in the completed integer ring. -/
theorem localIntegral_of_valuation_le (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h₁ : (v.valuation ℚ) E.a₁ ≤ 1) (h₂ : (v.valuation ℚ) E.a₂ ≤ 1)
    (h₃ : (v.valuation ℚ) E.a₃ ≤ 1) (h₄ : (v.valuation ℚ) E.a₄ ≤ 1)
    (h₆ : (v.valuation ℚ) E.a₆ ≤ 1) :
    WeierstrassCurve.IsIntegral (v.adicCompletionIntegers ℚ) (E.baseChange (v.adicCompletion ℚ)) := by
  apply WeierstrassCurve.isIntegral_of_exists_lift (v.adicCompletionIntegers ℚ)
  · refine ⟨⟨(E.baseChange (v.adicCompletion ℚ)).a₁, ?_⟩, rfl⟩
    simpa only [mem_adicCompletionIntegers, WeierstrassCurve.baseChange, map_a₁,
      valued_algebraMap_Q] using h₁
  · refine ⟨⟨(E.baseChange (v.adicCompletion ℚ)).a₂, ?_⟩, rfl⟩
    simpa only [mem_adicCompletionIntegers, WeierstrassCurve.baseChange, map_a₂,
      valued_algebraMap_Q] using h₂
  · refine ⟨⟨(E.baseChange (v.adicCompletion ℚ)).a₃, ?_⟩, rfl⟩
    simpa only [mem_adicCompletionIntegers, WeierstrassCurve.baseChange, map_a₃,
      valued_algebraMap_Q] using h₃
  · refine ⟨⟨(E.baseChange (v.adicCompletion ℚ)).a₄, ?_⟩, rfl⟩
    simpa only [mem_adicCompletionIntegers, WeierstrassCurve.baseChange, map_a₄,
      valued_algebraMap_Q] using h₄
  · refine ⟨⟨(E.baseChange (v.adicCompletion ℚ)).a₆, ?_⟩, rfl⟩
    simpa only [mem_adicCompletionIntegers, WeierstrassCurve.baseChange, map_a₆,
      valued_algebraMap_Q] using h₆

/-- Integral coefficients and a unit discriminant force the chosen minimal equation to be good. -/
theorem goodReductionAt_of_valuation_data (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (h₁ : (v.valuation ℚ) E.a₁ ≤ 1) (h₂ : (v.valuation ℚ) E.a₂ ≤ 1)
    (h₃ : (v.valuation ℚ) E.a₃ ≤ 1) (h₄ : (v.valuation ℚ) E.a₄ ≤ 1)
    (h₆ : (v.valuation ℚ) E.a₆ ≤ 1) (hΔ : (v.valuation ℚ) E.Δ = 1) : GoodReductionAt E v := by
  have hInt : WeierstrassCurve.IsIntegral (v.adicCompletionIntegers ℚ)
      (E.baseChange (v.adicCompletion ℚ)) := localIntegral_of_valuation_le E v h₁ h₂ h₃ h₄ h₆
  have hunit : IsUnit (integralModel (v.adicCompletionIntegers ℚ)
      (E.baseChange (v.adicCompletion ℚ))).Δ := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (integralModel (v.adicCompletionIntegers ℚ) (E.baseChange (v.adicCompletion ℚ))).Δ) = 1
    rw [integralModel_Δ_eq]
    simpa only [WeierstrassCurve.baseChange, map_Δ, valued_algebraMap_Q] using hΔ
  exact hasGoodReduction_minimal_of_integral_unit_Δ (v.adicCompletionIntegers ℚ)
    (E.baseChange (v.adicCompletion ℚ)) hunit

/-- A nonzero integer belongs to only finitely many rational prime ideals. -/
theorem finite_primes_containing_integer (n : ℤ) (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | (n : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have hn' : (n : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hn
  exact Set.Finite.preimage asIdeal_injective.injOn
    (Ring.HasFiniteQuotients.finite_setOfPred_mem (n : 𝓞 ℚ) hn')

/-- A nonzero integer is absent from almost every rational prime ideal. -/
theorem eventually_integer_notMem (n : ℤ) (hn : n ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite, (n : 𝓞 ℚ) ∉ v.asIdeal := by
  rw [Filter.eventually_cofinite]
  simpa only [not_not] using finite_primes_containing_integer n hn

/-- Any rational number is integral at almost every rational prime ideal. -/
theorem eventually_rational_valuation_le_one (x : ℚ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite, (v.valuation ℚ) x ≤ 1 := by
  have hd : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  filter_upwards [eventually_integer_notMem (x.den : ℤ) hd] with v hv
  apply Rat.valuation_le_one_iff_den.mpr
  simpa only [Int.cast_natCast] using hv

/-- Any nonzero rational number is a local unit at almost every rational prime ideal. -/
theorem eventually_rational_valuation_eq_one (x : ℚ) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite, (v.valuation ℚ) x = 1 := by
  have hn : x.num ≠ 0 := by
    intro h
    apply hx
    rw [← x.num_div_den, h]
    simp
  have hd : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  filter_upwards [eventually_integer_notMem x.num hn,
    eventually_integer_notMem (x.den : ℤ) hd] with v hvn hvd
  have hnum : (v.valuation ℚ) (x.num : ℚ) = 1 := by
    simpa only [map_intCast] using
      (valuation_eq_one_iff_notMem (K := ℚ) (v := v) (r := (x.num : 𝓞 ℚ))).mpr hvn
  have hden : (v.valuation ℚ) (x.den : ℚ) = 1 := by
    simpa only [map_natCast] using
      (valuation_eq_one_iff_notMem (K := ℚ) (v := v) (r := (x.den : 𝓞 ℚ))).mpr
        (by simpa only [Int.cast_natCast] using hvd)
  rw [← x.num_div_den, map_div₀, hnum, hden, div_one]

/-- An elliptic curve over the rationals has good minimal reduction at almost every prime ideal. -/
theorem goodReductionAt_cofinite (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite, GoodReductionAt E v := by
  have hΔ : E.Δ ≠ 0 := hE.isUnit.ne_zero
  filter_upwards [eventually_rational_valuation_le_one E.a₁,
    eventually_rational_valuation_le_one E.a₂, eventually_rational_valuation_le_one E.a₃,
    eventually_rational_valuation_le_one E.a₄, eventually_rational_valuation_le_one E.a₆,
    eventually_rational_valuation_eq_one E.Δ hΔ] with v h₁ h₂ h₃ h₄ h₆ hΔv
  exact goodReductionAt_of_valuation_data E v h₁ h₂ h₃ h₄ h₆ hΔv

/-- The same good-reduction assertion, with a finite exceptional set of rational primes. -/
theorem goodReductionAt_almost_all_primes (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) :
    ∃ S : Finset ℕ, ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S → GoodReductionAt E (primeIdealQ p hp) := by
  classical
  have hbad : {v : HeightOneSpectrum (𝓞 ℚ) | ¬ GoodReductionAt E v}.Finite :=
    Filter.eventually_cofinite.mp (goodReductionAt_cofinite E hE)
  refine ⟨hbad.toFinset.image (fun v => v.asIdeal.absNorm), fun p hp hnot => ?_⟩
  by_contra h
  apply hnot
  exact Finset.mem_image.mpr
    ⟨primeIdealQ p hp, hbad.mem_toFinset.mpr h, primeIdealQ_absNorm p hp⟩

/-- The prime-coefficient hypothesis occurring in the original Faltings interface. -/
def PrimeCoefficientsAgreeAlmostEverywhere (E₁ E₂ : WeierstrassCurve ℚ) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → E₁.LFunction p = E₂.LFunction p

/-- Equality of the genuine local polynomials at almost every rational prime ideal. -/
def LocalPolynomialsAgreeAlmostEverywhere (E₁ E₂ : WeierstrassCurve ℚ) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite, localPolynomialQ E₁ v = localPolynomialQ E₂ v

/-- A finite exceptional set of prime coefficients becomes a finite exceptional set of prime ideals. -/
theorem primeCoefficients_cofinite (E₁ E₂ : WeierstrassCurve ℚ)
    (h : PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite,
      E₁.LFunction v.asIdeal.absNorm = E₂.LFunction v.asIdeal.absNorm := by
  obtain ⟨S, hS⟩ := h
  have hn : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite, v.asIdeal.absNorm ∉ S := by
    rw [Filter.eventually_cofinite]
    simp only [not_not]
    exact Set.Finite.of_injOn
      (f := fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal.absNorm)
      (t := (S : Set ℕ)) (fun _ hv => hv) absNorm_rational_injective.injOn S.finite_toSet
  filter_upwards [hn] with v hv
  exact hS v.asIdeal.absNorm (prime_absNorm_rational v) hv

/-- Conversely, cofinite coefficient agreement produces the exact finite-set hypothesis. -/
theorem primeCoefficients_of_cofinite (E₁ E₂ : WeierstrassCurve ℚ)
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite,
      E₁.LFunction v.asIdeal.absNorm = E₂.LFunction v.asIdeal.absNorm) :
    PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂ := by
  classical
  have hbad : {v : HeightOneSpectrum (𝓞 ℚ) |
      ¬ E₁.LFunction v.asIdeal.absNorm = E₂.LFunction v.asIdeal.absNorm}.Finite :=
    Filter.eventually_cofinite.mp h
  refine ⟨hbad.toFinset.image (fun v => v.asIdeal.absNorm), fun p hp hnot => ?_⟩
  have hv : E₁.LFunction (primeIdealQ p hp).asIdeal.absNorm =
      E₂.LFunction (primeIdealQ p hp).asIdeal.absNorm := by
    by_contra hne
    apply hnot
    exact Finset.mem_image.mpr
      ⟨primeIdealQ p hp, hbad.mem_toFinset.mpr hne, primeIdealQ_absNorm p hp⟩
  simpa only [primeIdealQ_absNorm] using hv

/-- The complete arithmetic dictionary: almost-all prime coefficients and almost-all local polynomials agree. -/
theorem localPolynomials_cofinite_iff_primeCoefficients (E₁ E₂ : WeierstrassCurve ℚ)
    (h₁ : E₁.IsElliptic) (h₂ : E₂.IsElliptic) :
    LocalPolynomialsAgreeAlmostEverywhere E₁ E₂ ↔
      PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂ := by
  constructor
  · intro h
    apply primeCoefficients_of_cofinite E₁ E₂
    filter_upwards [h, goodReductionAt_cofinite E₁ h₁, goodReductionAt_cofinite E₂ h₂]
      with v hv hg₁ hg₂
    exact (localPolynomialQ_eq_iff E₁ E₂ v hg₁ hg₂).mp hv
  · intro h
    filter_upwards [primeCoefficients_cofinite E₁ E₂ h, goodReductionAt_cofinite E₁ h₁,
      goodReductionAt_cofinite E₂ h₂] with v hv hg₁ hg₂
    exact (localPolynomialQ_eq_iff E₁ E₂ v hg₁ hg₂).mpr hv

/-- Equal prime coefficients imply equal local reciprocal series, arithmetic factors, and rational Euler factors almost everywhere. -/
theorem localFactors_equal_cofinite (E₁ E₂ : WeierstrassCurve ℚ)
    (h₁ : E₁.IsElliptic) (h₂ : E₂.IsElliptic)
    (h : PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in cofinite,
      (E₁.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ) =
          (E₂.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ) ∧
        (E₁.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ) =
          (E₂.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ) ∧
        ∀ T : ℂ, localFactorValueQ E₁ v T = localFactorValueQ E₂ v T := by
  filter_upwards [primeCoefficients_cofinite E₁ E₂ h, goodReductionAt_cofinite E₁ h₁,
    goodReductionAt_cofinite E₂ h₂] with v hv hg₁ hg₂
  exact localFactors_eq_of_coeff_eq E₁ E₂ v hg₁ hg₂ hv

end AlmostAllPrimes

section HeckeNormalization

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable (M : ℕ) [NeZero M]

/-- The existing full Hecke-ring action transported to the genuine weight-two space on `Γ₀(M)`. -/
def heckeGamma0 (n : ℕ) :
    Module.End ℂ (CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) :=
  (TauCeti.cuspFormCharSpaceOneEquiv M 2).toLinearMap ∘ₗ
    HeckeRing.GL2.heckeRingHomCuspCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)
      (HeckeRing.GL2.heckeTCompositeGamma0 M n) ∘ₗ
        (TauCeti.cuspFormCharSpaceOneEquiv M 2).symm.toLinearMap

omit [NeZero M] in
/-- The trivial unit character is one exactly at indices prime to the level, and zero elsewhere. -/
theorem unitHom_one_apply (d : ℕ) :
    (MulChar.ofUnitHom (1 : (ZMod M)ˣ →* ℂˣ) : DirichletCharacter ℂ M) d =
      if Nat.Coprime d M then 1 else 0 := by
  by_cases hd : Nat.Coprime d M
  · rw [ite_eq_left hd, ← ZMod.coe_unitOfCoprime d hd, MulChar.ofUnitHom_coe]
    simp
  · rw [ite_eq_right hd, MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]

/-- Transport through the trivial-character equivalence preserves the underlying function. -/
theorem coe_heckeGamma0 (n : ℕ)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) :
    (⇑(heckeGamma0 M n g) : ℍ → ℂ) =
      ⇑(HeckeRing.GL2.heckeRingHomCuspCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)
        (HeckeRing.GL2.heckeTCompositeGamma0 M n)
          ((TauCeti.cuspFormCharSpaceOneEquiv M 2).symm g) :
        CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) := by
  simp only [heckeGamma0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]

/-- Restriction from `Γ₀(M)` to the trivial-character space preserves the underlying function. -/
theorem coe_restrict_trivial
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) :
    (⇑((TauCeti.cuspFormCharSpaceOneEquiv M 2).symm g :
      CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) : ℍ → ℂ) = ⇑g := by
  simp only [TauCeti.coe_cuspFormCharSpaceOneEquiv_symm_apply, CuspForm.coe_restrict]

/-- The weight-two divisor-sum normalization, at every positive index including the bad indices.
This is the trivial-character case of Diamond–Shurman, Proposition 5.3.1, and the normalization
of Shimura's operators on pp. 525–526 of the 1973 paper. -/
theorem qExpansion_heckeGamma0 (n : ℕ) (hn : n ≠ 0)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) (m : ℕ) :
    (qExpansion 1 (heckeGamma0 M n g)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (if Nat.Coprime d M then (d : ℂ) else 0) *
          (qExpansion 1 g).coeff (m * n / d ^ 2) := by
  rw [coe_heckeGamma0]
  have h := HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0
    hn ((TauCeti.cuspFormCharSpaceOneEquiv M 2).symm g) m
  rw [h]
  simp only [unitHom_one_apply, coe_restrict_trivial, show (2 : ℤ) - 1 = 1 by norm_num,
    zpow_one]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp

/-- At a good prime, `a_m(T_p g) = a_{mp}(g) + p a_{m/p}(g)`;
the second coefficient is zero when `p` does not divide `m`. -/
theorem heckeGamma0_prime_coeff (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) (m : ℕ) :
    (qExpansion 1 (heckeGamma0 M p g)).coeff m =
      (qExpansion 1 g).coeff (m * p) +
        if p ∣ m then (p : ℂ) * (qExpansion 1 g).coeff (m / p) else 0 := by
  rw [qExpansion_heckeGamma0 M p hp.ne_zero]
  have hcop : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hpM
  by_cases hpm : p ∣ m
  · have hidx : m * p / p ^ 2 = m / p := by
      obtain ⟨t, rfl⟩ := hpm
      rw [show p * t * p = t * p ^ 2 by ring,
        Nat.mul_div_cancel _ (pow_pos hp.pos 2), Nat.mul_div_cancel_left t hp.pos]
    rw [ite_eq_left hpm, Nat.gcd_eq_right hpm, hp.divisors,
      Finset.sum_insert (show 1 ∉ ({p} : Finset ℕ) by
        simp only [Finset.mem_singleton]
        exact hp.ne_one.symm), Finset.sum_singleton]
    simp [hcop, hidx]
  · rw [ite_eq_right hpm, (hp.coprime_iff_not_dvd.mpr hpm).symm.gcd_eq_one]
    simp

/-- Shimura's weight-two normalization stated entirely on the genuine cusp-form space.
It imposes no condition at the unused index zero. -/
def HasShimuraNormalization
    (T : ℕ → Module.End ℂ (CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2, ∀ m : ℕ,
    (qExpansion 1 (T n g)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (if Nat.Coprime d M then (d : ℂ) else 0) *
          (qExpansion 1 g).coeff (m * n / d ^ 2)

/-- The existing full Hecke action has Shimura's normalization at every positive index. -/
theorem heckeGamma0_hasShimuraNormalization : HasShimuraNormalization M (heckeGamma0 M) :=
  qExpansion_heckeGamma0 M

/-- The normalization determines the operator on actual cusp forms, not merely on formal coefficients. -/
theorem heckeGamma0_unique
    (T : ℕ → Module.End ℂ (CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2))
    (hT : HasShimuraNormalization M T) (n : ℕ) (hn : n ≠ 0) : T n = heckeGamma0 M n := by
  apply LinearMap.ext
  intro g
  apply DFunLike.coe_injective
  apply ZInQ.Contrib.RC53Assist.NewformPeriods.coe_eq_of_qExpansion_coeff_eq
  intro m hm
  rw [hT n hn g m, qExpansion_heckeGamma0 M n hn g m]

/-- The normalized common-eigenfunction hypothesis in Shimura's theorem, on the actual space. -/
def IsShimuraCommonEigenform
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) : Prop :=
  (qExpansion 1 g).coeff 1 = 1 ∧
    ∀ n : ℕ+, heckeGamma0 M n g = (qExpansion 1 g).coeff n • g

/-- A normalized full eigenform in the original interface satisfies Shimura's eigenrelations. -/
theorem normalizedFullEigenform_isShimuraEigenform
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g) :
    IsShimuraCommonEigenform M g := by
  obtain ⟨h₁, e, hχ, heq⟩ := h
  rcases e with ⟨f, χ, hmem, ev, heig, hnz⟩
  dsimp only at hχ heq
  subst χ
  have hfg : (⇑f : ℍ → ℂ) = ⇑g := funext heq
  have hf₁ : (qExpansion 1 f).coeff 1 = 1 := by
    rw [hfg]
    exact h₁
  let e' : HeckeRing.GL2.Eigenform M 2 :=
    { toCuspForm := f, χ := 1, mem_charSpace := hmem,
      eigenvalue := ev, isEigen := heig, ne_zero := hnz }
  have hFe : TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨f, hmem⟩ = g := by
    apply DFunLike.coe_injective
    rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
    exact hfg
  refine ⟨h₁, fun n => ?_⟩
  have hncoeff : (qExpansion 1 g).coeff n = ev n := by
    have hh := e'.qExpansion_coeff_eq_eigenvalue hf₁ n
    simpa only [e', hfg] using hh
  rw [hncoeff]
  unfold heckeGamma0
  change TauCeti.cuspFormCharSpaceOneEquiv M 2
    (HeckeRing.GL2.heckeRingHomCuspCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)
      (HeckeRing.GL2.heckeTCompositeGamma0 M n)
        ((TauCeti.cuspFormCharSpaceOneEquiv M 2).symm g)) = ev n • g
  rw [← hFe, LinearEquiv.symm_apply_apply, heig n, map_smul]

/-- Shimura's normalized eigenrelations construct a genuine full eigenform with trivial character. -/
theorem shimuraEigenform_isNormalizedFull
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : IsShimuraCommonEigenform M g) :
    ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g := by
  obtain ⟨h₁, heig⟩ := h
  have hg₀ : g ≠ 0 := by
    intro hg
    have hh := h₁
    rw [hg, FunLike.coe_zero, qExpansion_zero] at hh
    simp at hh
  let F := (TauCeti.cuspFormCharSpaceOneEquiv M 2).symm g
  have hF₀ : F ≠ 0 := by
    dsimp only [F]
    exact (LinearEquiv.map_eq_zero_iff (TauCeti.cuspFormCharSpaceOneEquiv M 2).symm).not.mpr hg₀
  have hf₀ : (F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) ≠ 0 :=
    fun hz => hF₀ (Subtype.ext hz)
  let e : HeckeRing.GL2.Eigenform M 2 :=
    { toCuspForm := (F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2)
      χ := 1
      mem_charSpace := F.2
      eigenvalue := fun n => (qExpansion 1 g).coeff n
      isEigen := fun n => by
        change HeckeRing.GL2.heckeRingHomCuspCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ)
          (HeckeRing.GL2.heckeTCompositeGamma0 M n) F = (qExpansion 1 g).coeff n • F
        apply (TauCeti.cuspFormCharSpaceOneEquiv M 2).injective
        rw [map_smul]
        have hF : TauCeti.cuspFormCharSpaceOneEquiv M 2 F = g :=
          LinearEquiv.apply_symm_apply _ g
        rw [hF]
        change heckeGamma0 M n g = (qExpansion 1 g).coeff n • g
        exact heig n
      ne_zero := hf₀ }
  exact ⟨h₁, e, rfl, fun τ => congrFun (coe_restrict_trivial M g) τ⟩

/-- The original normalized-full-eigenform predicate is exactly Shimura's common-eigenfunction predicate. -/
theorem normalizedFullEigenform_iff_shimuraCommonEigenform
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) :
    ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g ↔
      IsShimuraCommonEigenform M g :=
  ⟨normalizedFullEigenform_isShimuraEigenform M g, shimuraEigenform_isNormalizedFull M g⟩

end HeckeNormalization

section PointedIsogenies

open WeierstrassCurve.Affine

/-- The exact function-field dictionary for nonzero pointed maps of Weierstrass curves.
The field map is contravariant, and its restriction carries the source infinity to the target
infinity. This is the function-field portion of the isogeny translation; no scheme-to-function-field
functor is asserted. See Silverman, II.2 and III.4. -/
theorem nonempty_isogeny_iff_pointed_functionField_map (E₁ E₂ : WeierstrassCurve ℚ) :
    Nonempty (TauCeti.Isogeny E₁.toAffine E₂.toAffine) ↔
      ∃ σ : E₂.toAffine.FunctionField →ₐ[ℚ] E₁.toAffine.FunctionField,
        ((infinityPlace E₁.toAffine).comap σ.toRingHom).IsEquiv (infinityPlace E₂.toAffine) := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨φ.fieldPullback, φ.isEquiv_comap_infinityPlace⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨σ.comp (IsScalarTower.toAlgHom ℚ E₂.toAffine.CoordinateRing E₂.toAffine.FunctionField),
      (TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace σ).mpr hσ⟩⟩

/-- A pointed embedding of the actual function fields yields the required coordinate pullback. -/
def isogenyOfPointedFunctionFieldMap (E₁ E₂ : WeierstrassCurve ℚ)
    (σ : E₂.toAffine.FunctionField →ₐ[ℚ] E₁.toAffine.FunctionField)
    (hσ : ((infinityPlace E₁.toAffine).comap σ.toRingHom).IsEquiv (infinityPlace E₂.toAffine)) :
    TauCeti.Isogeny E₁.toAffine E₂.toAffine where
  pullback := σ.comp
    (IsScalarTower.toAlgHom ℚ E₂.toAffine.CoordinateRing E₂.toAffine.FunctionField)
  mapsInfinity :=
    (TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace σ).mpr hσ

/-- The resulting isogeny induces exactly the supplied function-field map. -/
theorem isogenyOfPointedFunctionFieldMap_fieldPullback (E₁ E₂ : WeierstrassCurve ℚ)
    (σ : E₂.toAffine.FunctionField →ₐ[ℚ] E₁.toAffine.FunctionField)
    (hσ : ((infinityPlace E₁.toAffine).comap σ.toRingHom).IsEquiv (infinityPlace E₂.toAffine)) :
    (isogenyOfPointedFunctionFieldMap E₁ E₂ σ hσ).fieldPullback = σ := by
  exact (TauCeti.Isogeny.fieldPullback_unique _ σ fun _ => rfl).symm

end PointedIsogenies

section EulerEvaluation

/-- Evaluation of the actual local polynomial at the analytic variable `q^{-s}`. -/
def localLFactorQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (s : ℂ) : ℂ :=
  localFactorValueQ E v ((v.asIdeal.absNorm : ℂ) ^ (-s))

/-- The usual good-prime Euler factor, with exactly the exponent `1 - 2s`. -/
theorem localLFactorQ_eq_of_good (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (h : GoodReductionAt E (primeIdealQ p hp)) (s : ℂ) :
    localLFactorQ E (primeIdealQ p hp) s =
      (1 - (E.LFunction p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (1 - 2 * s))⁻¹ := by
  rw [localLFactorQ, localFactorValueQ_eq_of_good E (primeIdealQ p hp) h]
  simp only [primeIdealQ_absNorm]
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcp : (p : ℂ) ^ ((2 : ℂ) * (-s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
    simpa using Complex.cpow_nat_mul (p : ℂ) 2 (-s)
  have hpow : (p : ℂ) * ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (1 - 2 * s) := by
    rw [show (1 : ℂ) - 2 * s = 1 + (2 : ℂ) * (-s) by ring,
      Complex.cpow_add _ _ hpC, Complex.cpow_one, hcp]
  rw [hpow]

/-- Almost-all coefficient agreement implies equality of the analytic evaluations of the local factors. -/
theorem localLFactors_equal_cofinite (E₁ E₂ : WeierstrassCurve ℚ)
    (h₁ : E₁.IsElliptic) (h₂ : E₂.IsElliptic)
    (h : PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ∀ s : ℂ, localLFactorQ E₁ v s = localLFactorQ E₂ v s := by
  filter_upwards [localFactors_equal_cofinite E₁ E₂ h₁ h₂ h] with v hv
  intro s
  exact hv.2.2 ((v.asIdeal.absNorm : ℂ) ^ (-s))

/-- The same local-factor agreement on the actual finite-place type of the rational number field. -/
theorem localLFactors_equal_cofinite_finitePlaces (E₁ E₂ : WeierstrassCurve ℚ)
    (h₁ : E₁.IsElliptic) (h₂ : E₂.IsElliptic)
    (h : PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂) :
    ∀ᶠ w : NumberField.FinitePlace ℚ in Filter.cofinite,
      ∀ s : ℂ, localLFactorQ E₁ w.maximalIdeal s = localLFactorQ E₂ w.maximalIdeal s := by
  have hi := localLFactors_equal_cofinite E₁ E₂ h₁ h₂ h
  rw [Filter.eventually_cofinite] at hi ⊢
  exact Set.Finite.of_injOn
    (f := fun w : NumberField.FinitePlace ℚ => w.maximalIdeal)
    (t := {v : HeightOneSpectrum (𝓞 ℚ) | ¬ ∀ s : ℂ, localLFactorQ E₁ v s = localLFactorQ E₂ v s})
    (fun _ hw => hw) NumberField.FinitePlace.maximalIdeal_injective.injOn hi

end EulerEvaluation

section FrobeniusDictionary

open Module
open scoped WithZero Classical

/-- The matrix of the genuine Galois action on the local elliptic-curve Tate module. -/
def localTateMatrixQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))
    (b : Basis (Fin 2) ℤ_[ℓ]
      (TauCeti.TateModule ℓ
        ((E.baseChange (v.adicCompletion ℚ)).baseChange
          (AlgebraicClosure (v.adicCompletion ℚ))).toAffine.Point)) :
    Matrix (Fin 2) (Fin 2) ℤ_[ℓ] :=
  LinearMap.toMatrix b b ((E.baseChange (v.adicCompletion ℚ)).tateModuleGaloisRepresentation ℓ σ)

/-- The Tate-module basis appearing below exists; the rank-two assertions are not vacuous. -/
theorem nonempty_localTateBasisQ (E : WeierstrassCurve ℚ) (hE : E.IsElliptic)
    (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (Basis (Fin 2) ℤ_[ℓ]
      (TauCeti.TateModule ℓ
        ((E.baseChange (v.adicCompletion ℚ)).baseChange
          (AlgebraicClosure (v.adicCompletion ℚ))).toAffine.Point)) := by
  have hℓ : (ℓ : AlgebraicClosure (v.adicCompletion ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨e⟩ := ((E.baseChange (v.adicCompletion ℚ)).baseChange
    (AlgebraicClosure (v.adicCompletion ℚ))).nonempty_linearEquiv_tateModule hℓ
  exact ⟨Basis.ofEquivFun e⟩

/-- Arithmetic Frobenius is the `q`-power map on the residue field of an algebraic closure. -/
def IsArithmeticFrobeniusOnClosureQ (v : HeightOneSpectrum (𝓞 ℚ))
    (Γ : Type*) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure (v.adicCompletion ℚ)) Γ)
    (σ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)) : Prop :=
  ∀ x : AlgebraicClosure (v.adicCompletion ℚ), w x ≤ 1 →
    w (σ x - x ^ v.asIdeal.absNorm) < 1

/-- The textbook Frobenius trace and determinant at good reduction, stated as an explicit
remaining classical proposition, not proved here. For every auxiliary prime different from `p`,
the actual Tate-module action of an arithmetic Frobenius has trace `p + 1 - #E(F_p)` and
determinant `p`, in every basis. The chosen valuation extends the local valuation up to
valuation equivalence. This statement combines the finite-field Frobenius polynomial and
good-reduction Tate specialization; see Silverman, V.2 and VII.7. It mentions neither printed
leaf nor the period conclusion. -/
def GoodReductionFrobeniusTraceDictionaryQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
    ∀ (p : ℕ) (hp : p.Prime), GoodReductionAt E (primeIdealQ p hp) →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
        ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
          (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
          (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
            (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
            (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
          ∀ σ : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ) ≃ₐ[
            (primeIdealQ p hp).adicCompletion ℚ]
              AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ),
            IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ →
            ∀ b : Basis (Fin 2) ℤ_[ℓ]
              (TauCeti.TateModule ℓ
                ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
                  (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point),
              Matrix.trace (localTateMatrixQ E (primeIdealQ p hp) ℓ σ b) =
                  (((p : ℤ) + 1 - (Nat.card (reducedCurveModP E p hp).toAffine.Point : ℤ)) : ℤ_[ℓ]) ∧
                Matrix.det (localTateMatrixQ E (primeIdealQ p hp) ℓ σ b) = (p : ℤ_[ℓ])

/-- The determinant normalization for a rank-two endomorphism, proved by its four entries. -/
theorem determinantEuler_polynomial {A : Type*} [CommRing A]
    (M : Matrix (Fin 2) (Fin 2) A) :
    Matrix.det ((1 : Matrix (Fin 2) (Fin 2) (Polynomial A)) -
      (Polynomial.X : Polynomial A) • M.map (Polynomial.C : A → Polynomial A)) =
        1 - Polynomial.C (Matrix.trace M) * Polynomial.X +
          Polynomial.C (Matrix.det M) * Polynomial.X ^ 2 := by
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply, Matrix.trace]
  simp
  ring

/-- Faltings's formal determinant factor, on the genuine elliptic-curve Tate module. -/
def tateEulerPolynomialQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))
    (b : Basis (Fin 2) ℤ_[ℓ]
      (TauCeti.TateModule ℓ
        ((E.baseChange (v.adicCompletion ℚ)).baseChange
          (AlgebraicClosure (v.adicCompletion ℚ))).toAffine.Point)) : Polynomial ℤ_[ℓ] :=
  Matrix.det ((1 : Matrix (Fin 2) (Fin 2) (Polynomial ℤ_[ℓ])) -
    (Polynomial.X : Polynomial ℤ_[ℓ]) •
      (localTateMatrixQ E v ℓ σ b).map (Polynomial.C : ℤ_[ℓ] → Polynomial ℤ_[ℓ]))

/-- The precise remaining Frobenius hypothesis discharges the determinant-versus-local-polynomial
comparison. All arithmetic normalization in this implication is proved, and the classical input
is displayed as a separate proposition. -/
theorem tateEulerPolynomialQ_eq_localPolynomial_of_dictionary
    (hD : GoodReductionFrobeniusTraceDictionaryQ)
    (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) (p : ℕ) (hp : p.Prime)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ)
    (hw : (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
      (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
      (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰))
    (σ : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ) ≃ₐ[
      (primeIdealQ p hp).adicCompletion ℚ]
        AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))
    (hσ : IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ)
    (b : Basis (Fin 2) ℤ_[ℓ]
      (TauCeti.TateModule ℓ
        ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
          (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point)) :
    tateEulerPolynomialQ E (primeIdealQ p hp) ℓ σ b =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℤ_[ℓ]) := by
  have hm := hD E hE p hp hgood ℓ hℓ Γ w hw σ hσ b
  have ht : Matrix.trace (localTateMatrixQ E (primeIdealQ p hp) ℓ σ b) =
      (E.LFunction p : ℤ_[ℓ]) := by
    rw [lFunction_prime_eq_card_ZMod E p hp hgood]
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast] using hm.1
  rw [tateEulerPolynomialQ, determinantEuler_polynomial, ht, hm.2,
    localPolynomialQ_eq_of_good E (primeIdealQ p hp) hgood, primeIdealQ_absNorm]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_pow, Polynomial.map_one]
  rfl

/-- Equality of Faltings's formal determinant factors at a rational prime, for every auxiliary
prime and every basis of the genuine local Tate modules, with the same arithmetic Frobenius lift. -/
def TateEulerPolynomialsAgreeAtPrime (E₁ E₂ : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
    ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ]
      (w : Valuation (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)) Γ),
      (w.comap (algebraMap ((primeIdealQ p hp).adicCompletion ℚ)
        (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ)))).IsEquiv
        (Valued.v : Valuation ((primeIdealQ p hp).adicCompletion ℚ) ℤᵐ⁰) →
      ∀ σ : AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ) ≃ₐ[
        (primeIdealQ p hp).adicCompletion ℚ]
          AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ),
        IsArithmeticFrobeniusOnClosureQ (primeIdealQ p hp) Γ w σ →
        ∀ b₁ : Basis (Fin 2) ℤ_[ℓ]
          (TauCeti.TateModule ℓ
            ((E₁.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
              (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point),
        ∀ b₂ : Basis (Fin 2) ℤ_[ℓ]
          (TauCeti.TateModule ℓ
            ((E₂.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).baseChange
              (AlgebraicClosure ((primeIdealQ p hp).adicCompletion ℚ))).toAffine.Point),
          tateEulerPolynomialQ E₁ (primeIdealQ p hp) ℓ σ b₁ =
            tateEulerPolynomialQ E₂ (primeIdealQ p hp) ℓ σ b₂

/-- Equal coefficients at almost all primes imply equal genuine Frobenius determinant factors
at almost all primes, conditional only on the displayed textbook trace-and-determinant dictionary. -/
theorem tateEulerPolynomials_equal_almost_all_primes
    (hD : GoodReductionFrobeniusTraceDictionaryQ)
    (E₁ E₂ : WeierstrassCurve ℚ) (h₁ : E₁.IsElliptic) (h₂ : E₂.IsElliptic)
    (h : PrimeCoefficientsAgreeAlmostEverywhere E₁ E₂) :
    ∃ S : Finset ℕ, ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S →
      TateEulerPolynomialsAgreeAtPrime E₁ E₂ p hp := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨S₁, hS₁⟩ := goodReductionAt_almost_all_primes E₁ h₁
  obtain ⟨S₂, hS₂⟩ := goodReductionAt_almost_all_primes E₂ h₂
  refine ⟨(S ∪ S₁) ∪ S₂, fun p hp hnot => ?_⟩
  simp only [Finset.mem_union, not_or] at hnot
  have hc := hS p hp hnot.1.1
  have hg₁ := hS₁ p hp hnot.1.2
  have hg₂ := hS₂ p hp hnot.2
  intro ℓ hfact hℓ Γ hΓ w hw σ hσ b₁ b₂
  rw [tateEulerPolynomialQ_eq_localPolynomial_of_dictionary hD E₁ h₁ p hp hg₁ ℓ hℓ
      Γ w hw σ hσ b₁,
    tateEulerPolynomialQ_eq_localPolynomial_of_dictionary hD E₂ h₂ p hp hg₂ ℓ hℓ
      Γ w hw σ hσ b₂]
  apply congrArg (fun P : ℤ[X] => P.map (Int.castRingHom ℤ_[ℓ]))
  apply (localPolynomialQ_eq_iff E₁ E₂ (primeIdealQ p hp) hg₁ hg₂).mpr
  simpa only [primeIdealQ_absNorm] using hc

end FrobeniusDictionary

section PrintedInterfaces

open CongruenceSubgroup UpperHalfPlane WeierstrassCurve.Affine
open ZInQ.Contrib.RC53Assist.NewformPeriods

/-- The linear term of the actual local polynomial reads the global prime coefficient,
including at the bad primes. -/
theorem lFunction_prime_eq_neg_localPolynomial_coeff (E : WeierstrassCurve ℚ)
    (p : ℕ) (hp : p.Prime) :
    E.LFunction p = -(localPolynomialQ E (primeIdealQ p hp)).coeff 1 := by
  have h := lFunction_at_primeIdeal E (primeIdealQ p hp)
  rw [primeIdealQ_absNorm, WeierstrassCurve.localPowerSeries, invOfUnit_coeff_one,
    Polynomial.coeff_coe] at h
  exact h

/-- Equality of the rational Euler polynomial with `1 - bT + pT²` gives exactly the coefficient
conclusion in the original Shimura interface. -/
theorem primeCoefficient_eq_of_localPolynomial_form (E : WeierstrassCurve ℚ)
    (p : ℕ) (hp : p.Prime) (b : ℚ)
    (hP : (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ) =
      1 - C b * X + C (p : ℚ) * X ^ 2) : (E.LFunction p : ℚ) = b := by
  have hc := congrArg (fun P : ℚ[X] => P.coeff 1) hP
  have hc' : ((localPolynomialQ E (primeIdealQ p hp)).coeff 1 : ℚ) = -b := by
    simpa [Polynomial.coeff_one] using hc
  rw [lFunction_prime_eq_neg_localPolynomial_coeff E p hp, Int.cast_neg, hc']
  simp

/-- Conversely, the prime coefficient determines the rational good-reduction Euler polynomial. -/
theorem localPolynomial_form_of_primeCoefficient (E : WeierstrassCurve ℚ)
    (p : ℕ) (hp : p.Prime) (hgood : GoodReductionAt E (primeIdealQ p hp)) (b : ℚ)
    (hc : (E.LFunction p : ℚ) = b) :
    (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ) =
      1 - C b * X + C (p : ℚ) * X ^ 2 := by
  rw [localPolynomialQ_eq_of_good E (primeIdealQ p hp) hgood, primeIdealQ_absNorm]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_pow, Polynomial.map_one]
  change 1 - C (E.LFunction p : ℚ) * X + C ((p : ℤ) : ℚ) * X ^ 2 =
    1 - C b * X + C (p : ℚ) * X ^ 2
  rw [hc, Int.cast_natCast]

/-- Shimura's rational weight-two consequence form with the common-eigenfunction normalization
and explicit good-prime Euler polynomials. The modular point and differential clauses are the
same coordinate clauses as in the original interface. Their geometric readings remain open:
the standard modular curve, the one-dimensional abelian quotient, and pullback of differentials.
Source: Shimura 1973, Theorem 1, pp. 525–526. This is a proposition, not a proof of that theorem. -/
def Shimura1973EulerPolynomialFormQ : Prop :=
  ∀ (M : ℕ) [NeZero M] (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2),
    IsShimuraCommonEigenform M g →
    ∀ b : ℕ → ℚ, (∀ n : ℕ, (qExpansion 1 g).coeff n = (b n : ℂ)) →
      ∃ A : WeierstrassCurve ℚ, A.IsElliptic ∧
        ∃ x y : LaurentSeries ℚ, IsModularPointQ M A x y ∧
          (∃ c : ℂ, PullbackIsMultiple A x y (qExpansion 1 g) c) ∧
          ∃ S : Finset ℕ, ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S →
            ¬ p ∣ M ∧ GoodReductionAt A (primeIdealQ p hp) ∧
              (localPolynomialQ A (primeIdealQ p hp)).map (Int.castRingHom ℚ) =
                1 - C (b p) * X + C (p : ℚ) * X ^ 2

/-- The polynomial form yields the exact Shimura conclusion consumed by the reduction. -/
theorem shimuraLeaf_of_eulerPolynomialForm (hS : Shimura1973EulerPolynomialFormQ) :
    Shimura1973Thm1RationalGamma0 := by
  intro M hM g heig b hb
  obtain ⟨A, hA, x, y, hpt, hpull, S, hS'⟩ :=
    hS M g (normalizedFullEigenform_isShimuraEigenform M g heig) b hb
  refine ⟨A, hA, x, y, hpt, hpull, S, fun p hp hnot => ?_⟩
  exact primeCoefficient_eq_of_localPolynomial_form A p hp (b p) (hS' p hp hnot).2.2

/-- The original Shimura leaf gives the polynomial form after enlarging the finite exceptional
set by the bad-reduction primes and the primes of the level. -/
theorem eulerPolynomialForm_of_shimuraLeaf (hS : Shimura1973Thm1RationalGamma0) :
    Shimura1973EulerPolynomialFormQ := by
  intro M hM g heig b hb
  obtain ⟨A, hA, x, y, hpt, hpull, S, hS'⟩ :=
    hS M g (shimuraEigenform_isNormalizedFull M g heig) b hb
  obtain ⟨Sgood, hgood⟩ := goodReductionAt_almost_all_primes A hA
  refine ⟨A, hA, x, y, hpt, hpull, (S ∪ Sgood) ∪ M.primeFactors, fun p hp hnot => ?_⟩
  simp only [Finset.mem_union, not_or] at hnot
  have hnotLevel : ¬ p ∣ M := by
    intro hdiv
    exact hnot.2 (Nat.mem_primeFactors.mpr ⟨hp, hdiv, NeZero.ne M⟩)
  have hg := hgood p hp hnot.1.2
  refine ⟨hnotLevel, hg, ?_⟩
  exact localPolynomial_form_of_primeCoefficient A p hp hg (b p) (hS' p hp hnot.1.1)

/-- The two specialized Shimura interfaces have exactly the same conditional content. -/
theorem shimura_eulerPolynomialForm_iff :
    Shimura1973EulerPolynomialFormQ ↔ Shimura1973Thm1RationalGamma0 :=
  ⟨shimuraLeaf_of_eulerPolynomialForm, eulerPolynomialForm_of_shimuraLeaf⟩

/-- Faltings's elliptic-curve consequence form with local polynomials and pointed function-field
maps. Source: Faltings 1983, §5, Korollar 2, iii ⇒ i, p. 361. This is a proposition, not a proof
of the printed theorem. Reading its local polynomials as Tate determinants requires the displayed
Frobenius dictionary; the scheme-to-Weierstrass and scheme-to-function-field readings remain open. -/
def Faltings1983LocalPolynomialFormQ : Prop :=
  ∀ E₁ E₂ : WeierstrassCurve ℚ, E₁.IsElliptic → E₂.IsElliptic →
    LocalPolynomialsAgreeAlmostEverywhere E₁ E₂ →
      ∃ σ : E₂.toAffine.FunctionField →ₐ[ℚ] E₁.toAffine.FunctionField,
        ((infinityPlace E₁.toAffine).comap σ.toRingHom).IsEquiv (infinityPlace E₂.toAffine)

/-- The local-polynomial and function-field version gives the exact original Faltings interface. -/
theorem faltingsLeaf_of_localPolynomialForm (hF : Faltings1983LocalPolynomialFormQ) :
    Faltings1983Kor2EllipticQ := by
  intro E₁ E₂ h₁ h₂ hcoeff
  have hpoly := (localPolynomials_cofinite_iff_primeCoefficients E₁ E₂ h₁ h₂).mpr hcoeff
  obtain ⟨σ, hσ⟩ := hF E₁ E₂ h₁ h₂ hpoly
  exact ⟨isogenyOfPointedFunctionFieldMap E₁ E₂ σ hσ⟩

/-- Conversely, the original Faltings leaf yields its local-polynomial and function-field version. -/
theorem localPolynomialForm_of_faltingsLeaf (hF : Faltings1983Kor2EllipticQ) :
    Faltings1983LocalPolynomialFormQ := by
  intro E₁ E₂ h₁ h₂ hpoly
  have hcoeff := (localPolynomials_cofinite_iff_primeCoefficients E₁ E₂ h₁ h₂).mp hpoly
  obtain ⟨φ⟩ := hF E₁ E₂ h₁ h₂ hcoeff
  exact ⟨φ.fieldPullback, φ.isEquiv_comap_infinityPlace⟩

/-- The two specialized Faltings interfaces have exactly the same conditional content. -/
theorem faltings_localPolynomialForm_iff :
    Faltings1983LocalPolynomialFormQ ↔ Faltings1983Kor2EllipticQ :=
  ⟨faltingsLeaf_of_localPolynomialForm, localPolynomialForm_of_faltingsLeaf⟩

/-- The original some-level period conclusion follows from the reformulated leaves and the
unchanged three geometric gluing propositions. -/
theorem someLevelPeriodsRational_of_dictionaryLeaves
    (hS : Shimura1973EulerPolynomialFormQ) (hF : Faltings1983LocalPolynomialFormQ)
    (h₀ : NewformOfModularCurveGlue) (h₁ : ParametrizationPeriodsGlue)
    (h₂ : IsogenyLatticeGlue) : SomeLevelPeriodsRational :=
  someLevelPeriodsRational_of_prints (shimuraLeaf_of_eulerPolynomialForm hS)
    (faltingsLeaf_of_localPolynomialForm hF) h₀ h₁ h₂

/-- The exact original rational-period conclusion, with no change of target or quantifier order. -/
theorem newformPeriodsRational_of_dictionaryLeaves
    (hS : Shimura1973EulerPolynomialFormQ) (hF : Faltings1983LocalPolynomialFormQ)
    (h₀ : NewformOfModularCurveGlue) (h₁ : ParametrizationPeriodsGlue)
    (h₂ : IsogenyLatticeGlue) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.NewformPeriodsRational :=
  newformPeriodsRational_of_prints (shimuraLeaf_of_eulerPolynomialForm hS)
    (faltingsLeaf_of_localPolynomialForm hF) h₀ h₁ h₂

/-- The corresponding exact weak-Weil conclusion of the unchanged assembly. -/
theorem modularToWeakWeil_of_dictionaryLeaves
    (hS : Shimura1973EulerPolynomialFormQ) (hF : Faltings1983LocalPolynomialFormQ)
    (h₀ : NewformOfModularCurveGlue) (h₁ : ParametrizationPeriodsGlue)
    (h₂ : IsogenyLatticeGlue) : ZInQ.Contrib.CloudB3RC53.ModularToWeakWeil :=
  modularToWeakWeil_of_prints (shimuraLeaf_of_eulerPolynomialForm hS)
    (faltingsLeaf_of_localPolynomialForm hF) h₀ h₁ h₂

end PrintedInterfaces

end ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary
