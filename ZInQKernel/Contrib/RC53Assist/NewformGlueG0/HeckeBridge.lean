import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.NewformGlue
import ZInQKernel.Contrib.RC53Assist.NewformPeriodsDictionary.Dictionary
import TauCeti.NumberTheory.ArithmeticFunction.PrimeRecurrence

/-!
# The arithmetic Hecke bridge for a modular elliptic curve

The coefficients used here are those of the existing Euler product
`WeierstrassCurve.LFunction`, not an unspecified sequence. The local polynomials
and their reciprocal power series are the existing minimal-reduction objects.

This file proves the coefficient recurrence at a prime of good reduction, hence
the actual Hecke eigenvector equation whenever that prime does not divide the
level of the supplied cusp form. Good reduction outside a finite set is already
proved in `NewformPeriodsDictionary/Dictionary.lean`. No assertion that the
curve is good at every prime outside the level is assumed.

The newform existence step is the old/new decomposition of Li 1975, §2,
p. 294, and Theorem 3, p. 295, in the existing divisor-level newform API.
Agreement at almost all good primes is distinct from agreement at the bad
primes: the latter requires the Galois and local-factor comparisons.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0

open ArithmeticFunction NumberField IsDedekindDomain
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

section EulerProduct

variable {B ι : Type*} [CommSemiring B]

/-- **PROVED**, from the definition of `ArithmeticFunction.ofPowerSeries`
(Mathlib, `NumberTheory/ArithmeticFunction/LFunction.lean`): a normalized
local factor is the convolution unit at an index not divisible by its base. -/
theorem ofPowerSeries_apply_eq_one_of_not_dvd {q n : ℕ} (hq : 1 < q)
    (f : PowerSeries B) (hf : f.constantCoeff = 1) (hqn : ¬q ∣ n) :
    ArithmeticFunction.ofPowerSeries q f n = (1 : ArithmeticFunction B) n := by
  classical
  by_cases hn : n = 1
  · subst n
    rw [ArithmeticFunction.ofPowerSeries_apply_one, hf]
    simp
  · rw [ArithmeticFunction.ofPowerSeries_apply hq,
      Function.extend_apply', Pi.zero_apply, ArithmeticFunction.one_apply_ne hn]
    rintro ⟨r, hr⟩
    cases r with
    | zero => exact hn (by simpa using hr.symm)
    | succ r =>
      apply hqn
      exact ⟨q ^ r, hr.symm.trans (pow_succ' q r)⟩

/-- **PROVED**, by the divisor formula for Dirichlet convolution (Mathlib,
`ArithmeticFunction.mul_apply`): a normalized local factor can be removed
when its base does not divide the index. -/
theorem ofPowerSeries_mul_apply_of_not_dvd {q n : ℕ} (hq : 1 < q)
    (f : PowerSeries B) (hf : f.constantCoeff = 1) (hqn : ¬q ∣ n)
    (g : ArithmeticFunction B) :
    (ArithmeticFunction.ofPowerSeries q f * g) n = g n := by
  classical
  conv_rhs => rw [← one_mul g]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ofPowerSeries_apply_eq_one_of_not_dvd hq f hf]
  exact fun hqd => hqn
    (hqd.trans (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hd)))

/-- **PROVED**, by induction on a finite product of local factors; locator:
`ofPowerSeries_mul_apply_of_not_dvd`. All the factors supported away from
an index may be removed from a Dirichlet convolution at that index. -/
theorem finsetProduct_mul_apply_of_forall_not_dvd (q : ι → ℕ)
    (f : ι → PowerSeries B) (hq : ∀ i, 1 < q i)
    (hf : ∀ i, (f i).constantCoeff = 1) (s : Finset ι) (n : ℕ)
    (hqn : ∀ i ∈ s, ¬q i ∣ n) (g : ArithmeticFunction B) :
    ((∏ i ∈ s, ArithmeticFunction.ofPowerSeries (q i) (f i)) * g) n = g n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, mul_assoc,
      ofPowerSeries_mul_apply_of_not_dvd (hq i) (f i) (hf i)
        (hqn i (Finset.mem_insert_self i s))]
    exact ih (fun j hj => hqn j (Finset.mem_insert_of_mem hj))

/-- **PROVED**, from pointwise convergence of the existing Euler product
(Mathlib, `ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries`): with
pairwise distinct prime bases, the coefficient at a power of one prime is
exactly the corresponding local reciprocal coefficient. -/
theorem eulerProduct_at_prime_pow (q : ι → ℕ) [Northcott q]
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (f : ι → PowerSeries B) (hf : ∀ i, (f i).constantCoeff = 1)
    (i : ι) (r : ℕ) :
    ArithmeticFunction.eulerProduct
      (fun j => ArithmeticFunction.ofPowerSeries (q j) (f j)) (q i ^ r) =
        (f i).coeff r := by
  classical
  have hpartial : ∀ s : Finset ι, i ∈ s →
      (∏ j ∈ s, ArithmeticFunction.ofPowerSeries (q j) (f j)) (q i ^ r) =
        (f i).coeff r := by
    intro s his
    rw [← Finset.prod_erase_mul s _ his]
    rw [finsetProduct_mul_apply_of_forall_not_dvd q f
      (fun j => (hq j).one_lt) hf (s.erase i) (q i ^ r)]
    · exact ArithmeticFunction.ofPowerSeries_apply_pow (hq i).one_lt (f i) r
    · intro j hj hjd
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hdiv : q j ∣ q i := (hq j).dvd_of_dvd_pow hjd
      have heq : q j = q i :=
        ((hq i).eq_one_or_self_of_dvd (q j) hdiv).resolve_left (hq j).ne_one
      exact hji (hinj heq)
  have he := ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries q f hf (q i ^ r)
  have hi : ∀ᶠ s : Finset ι in Filter.atTop, i ∈ s :=
    Filter.eventually_atTop.mpr ⟨{i}, fun s hs => hs (Finset.mem_singleton_self i)⟩
  obtain ⟨s, hs, his⟩ := (he.and hi).exists
  exact hs.symm.trans (hpartial s his)

end EulerProduct

section EllipticCoefficients

open Polynomial

/-- **PROVED**, from `ArithmeticFunction.isMultiplicative_eulerProduct`
and normalized prime-supported local factors. Locator: the definition of
`WeierstrassCurve.LFunction` and `localPowerSeries_constantCoeff` in
`NewformPeriodsDictionary/Dictionary.lean`. -/
theorem lFunction_isMultiplicative (E : WeierstrassCurve ℚ) :
    ArithmeticFunction.IsMultiplicative E.LFunction := by
  unfold WeierstrassCurve.LFunction
  apply ArithmeticFunction.isMultiplicative_eulerProduct
  intro v
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · rw [card_residueField_completion]
    exact (prime_absNorm_rational v).isPrimePow
  · exact localPowerSeries_constantCoeff _ _

/-- **PROVED**, from multiplicativity of the existing Euler product; locator:
`lFunction_isMultiplicative`. In particular every supplied modular form
with these positive coefficients is normalized. -/
theorem lFunction_one (E : WeierstrassCurve ℚ) : E.LFunction 1 = 1 :=
  (lFunction_isMultiplicative E).1

/-- **PROVED**, by prime support and Euler-product convergence; locators:
`eulerProduct_at_prime_pow` and the completed-residue cardinality dictionary.
This holds at bad primes as well as good primes. -/
theorem lFunction_prime_pow (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) (r : ℕ) :
    E.LFunction (p ^ r) =
      ((E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).localPowerSeries
        ((primeIdealQ p hp).adicCompletionIntegers ℚ)).coeff r := by
  let q := fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
  let f := fun v : HeightOneSpectrum (𝓞 ℚ) =>
    (E.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)
  have hq : ∀ v, (q v).Prime := by
    intro v
    simpa only [q, card_residueField_completion] using prime_absNorm_rational v
  have hinj : Function.Injective q := by
    intro v w h
    apply absNorm_rational_injective
    simpa only [q, card_residueField_completion] using h
  have : Northcott q := residueCard_northcott ℚ
  have hf : ∀ v, (f v).constantCoeff = 1 := fun v => localPowerSeries_constantCoeff _ _
  have h := eulerProduct_at_prime_pow q hq hinj f hf (primeIdealQ p hp) r
  have hL : E.LFunction = ArithmeticFunction.eulerProduct
      (fun v => ArithmeticFunction.ofPowerSeries (q v) (f v)) := by
    unfold WeierstrassCurve.LFunction
    apply congrArg ArithmeticFunction.eulerProduct
    funext v
    dsimp only [q, f, WeierstrassCurve.localEulerFactor]
    apply congrArg (ArithmeticFunction.ofPowerSeries
      (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))))
    apply congrArg (fun W : WeierstrassCurve (v.adicCompletion ℚ) =>
      W.localPowerSeries (v.adicCompletionIntegers ℚ))
    unfold WeierstrassCurve.baseChange
    apply congrArg (WeierstrassCurve.map E)
    exact Subsingleton.elim _ _
  rw [hL]
  simpa only [q, f, card_residueField_completion, primeIdealQ_absNorm] using h

/-- **PROVED**, by multiplying a quadratic polynomial by its formal reciprocal;
locator: Mathlib `PowerSeries.mul_invOfUnit`. This is the purely algebraic
engine of the weight-two Hecke prime-power recurrence. -/
theorem reciprocal_quadratic_recurrence (a d : ℤ) (r : ℕ) :
    let P : PowerSeries ℤ := 1 - PowerSeries.C a * PowerSeries.X +
      PowerSeries.C d * PowerSeries.X ^ 2
    (PowerSeries.invOfUnit P 1).coeff (r + 2) =
      a * (PowerSeries.invOfUnit P 1).coeff (r + 1) -
        d * (PowerSeries.invOfUnit P 1).coeff r := by
  dsimp only
  let P : PowerSeries ℤ := 1 - PowerSeries.C a * PowerSeries.X +
    PowerSeries.C d * PowerSeries.X ^ 2
  let S := PowerSeries.invOfUnit P 1
  have hP : P.constantCoeff = (1 : ℤˣ) := by simp [P]
  have hmul : P * S = 1 := PowerSeries.mul_invOfUnit P 1 hP
  have hc := congrArg (PowerSeries.coeff (r + 2)) hmul
  change (P * S).coeff (r + 2) = _ at hc
  simp only [P, add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_one,
    show r + 2 ≠ 0 by omega, ite_false] at hc
  change S.coeff (r + 2) = a * S.coeff (r + 1) - d * S.coeff r
  linear_combination hc

/-- **PROVED**, from the actual good-reduction local polynomial and its formal
reciprocal. Locators: `localPolynomialQ_eq_of_good`, `lFunction_prime_pow`,
and `reciprocal_quadratic_recurrence`. No Frobenius representation is assumed. -/
theorem lFunction_good_prime_pow_recurrence (E : WeierstrassCurve ℚ)
    (p : ℕ) (hp : p.Prime) (hgood : GoodReductionAt E (primeIdealQ p hp)) (r : ℕ) :
    E.LFunction (p ^ (r + 2)) = E.LFunction p * E.LFunction (p ^ (r + 1)) -
      (p : ℤ) * E.LFunction (p ^ r) := by
  have hP := localPolynomialQ_eq_of_good E (primeIdealQ p hp) hgood
  simp only [primeIdealQ_absNorm] at hP
  have hS : (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).localPowerSeries
      ((primeIdealQ p hp).adicCompletionIntegers ℚ) =
      PowerSeries.invOfUnit
        (1 - PowerSeries.C (E.LFunction p) * PowerSeries.X +
          PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2) 1 := by
    rw [WeierstrassCurve.localPowerSeries]
    change PowerSeries.invOfUnit (localPolynomialQ E (primeIdealQ p hp) : PowerSeries ℤ) 1 = _
    conv_lhs => rw [hP]
    simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X]
  rw [lFunction_prime_pow E p hp, lFunction_prime_pow E p hp,
    lFunction_prime_pow E p hp, hS]
  exact reciprocal_quadratic_recurrence (E.LFunction p) (p : ℤ) r

/-- **PROVED**, by prime-power recurrence and coprime multiplicativity.
Locator: `TauCeti.prime_mul_eq_of_prime_pow_recurrence_of_coprime_mul_eq`,
the coefficient criterion underlying Li 1975, Theorem 3, p. 295. -/
theorem lFunction_good_prime_mul (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) (m : ℕ) :
    E.LFunction (p * m) = E.LFunction p * E.LFunction m -
      if p ∣ m then (p : ℤ) * E.LFunction (m / p) else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact TauCeti.prime_mul_eq_of_prime_pow_recurrence_of_coprime_mul_eq
      (L := 1) hp (Nat.coprime_one_right p)
      (fun u v huv _ _ => (lFunction_isMultiplicative E).2 huv)
      (lFunction_good_prime_pow_recurrence E p hp hgood) m hm.ne'
      (Nat.coprime_one_right m)

/-- **PROVED**, by the four cases of the existing local-polynomial definition.
Locator: Mathlib `WeierstrassCurve.localPolynomial`.
At every reduction type the local polynomial is determined by its linear
and quadratic coefficients and has constant coefficient one. -/
theorem localPolynomial_quadratic_shape (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (E : WeierstrassCurve K) :
    E.localPolynomial R = 1 - C (-(E.localPolynomial R).coeff 1) * X +
      C ((E.localPolynomial R).coeff 2) * X ^ 2 := by
  classical
  unfold WeierstrassCurve.localPolynomial
  split_ifs <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]

/-- **PROVED**, from the actual global prime coefficient and local reciprocal.
Locators: `localPolynomial_quadratic_shape` and
`NewformPeriodsDictionary.lFunction_prime_eq_neg_localPolynomial_coeff`.
This includes the linear and constant bad-prime polynomials. -/
theorem localPolynomialQ_shape (E : WeierstrassCurve ℚ) (p : ℕ) (hp : p.Prime) :
    localPolynomialQ E (primeIdealQ p hp) = 1 - C (E.LFunction p) * X +
      C ((localPolynomialQ E (primeIdealQ p hp)).coeff 2) * X ^ 2 := by
  rw [lFunction_prime_eq_neg_localPolynomial_coeff E p hp]
  exact localPolynomial_quadratic_shape ((primeIdealQ p hp).adicCompletionIntegers ℚ)
    (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ))

/-- **PROVED**, from the true local polynomial and Euler-product prime-power
coefficients. Locators: `localPolynomialQ_shape`, `lFunction_prime_pow`,
and `reciprocal_quadratic_recurrence`.
This is a uniform recurrence at good and bad primes: its quadratic scalar
is the actual quadratic coefficient of the local polynomial. -/
theorem lFunction_prime_pow_recurrence (E : WeierstrassCurve ℚ) (p : ℕ)
    (hp : p.Prime) (r : ℕ) :
    E.LFunction (p ^ (r + 2)) = E.LFunction p * E.LFunction (p ^ (r + 1)) -
      (localPolynomialQ E (primeIdealQ p hp)).coeff 2 * E.LFunction (p ^ r) := by
  have hP := localPolynomialQ_shape E p hp
  have hS : (E.baseChange ((primeIdealQ p hp).adicCompletion ℚ)).localPowerSeries
      ((primeIdealQ p hp).adicCompletionIntegers ℚ) =
      PowerSeries.invOfUnit
        (1 - PowerSeries.C (E.LFunction p) * PowerSeries.X +
          PowerSeries.C ((localPolynomialQ E (primeIdealQ p hp)).coeff 2) *
            PowerSeries.X ^ 2) 1 := by
    rw [WeierstrassCurve.localPowerSeries]
    change PowerSeries.invOfUnit (localPolynomialQ E (primeIdealQ p hp) : PowerSeries ℤ) 1 = _
    conv_lhs => rw [hP]
    simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X]
  rw [lFunction_prime_pow E p hp, lFunction_prime_pow E p hp,
    lFunction_prime_pow E p hp, hS]
  exact reciprocal_quadratic_recurrence (E.LFunction p)
    ((localPolynomialQ E (primeIdealQ p hp)).coeff 2) r

/-- **PROVED**, by induction through prime powers and coprime products.
Locator: Mathlib `Nat.recOnPrimeCoprime` and `Nat.twoStepInduction`.
Two multiplicative arithmetic functions with the same prime coefficients
and the same prime-power recurrence scalars are equal. This is an algebraic
assembly theorem, not a newform-existence input. -/
theorem arithmeticFunction_eq_of_prime_recurrences {B : Type*} [CommRing B]
    (a b : ArithmeticFunction B) (ha : a.IsMultiplicative) (hb : b.IsMultiplicative)
    (d : ℕ → B) (hp : ∀ p : ℕ, p.Prime → a p = b p)
    (har : ∀ (p : ℕ), p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - d p * a (p ^ r))
    (hbr : ∀ (p : ℕ), p.Prime → ∀ r : ℕ,
      b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - d p * b (p ^ r)) : a = b := by
  ext n
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p r hprime =>
    induction r using Nat.twoStepInduction with
    | zero => simpa only [pow_zero] using ha.1.trans hb.1.symm
    | one => simpa only [pow_one] using hp p hprime
    | more r ih₁ ih₂ =>
      rw [har p hprime r, hbr p hprime r, hp p hprime, ih₁, ih₂]
  | coprime m n _ _ hmn hm hn =>
    rw [ha.2 hmn, hb.2 hmn, hm, hn]

end EllipticCoefficients

section HeckeBridge

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2 TauCeti Polynomial

/-- **PROVED**, using the cusp condition at infinity and the arithmetic
function's zero coefficient. Locator: `CuspFormClass.qExpansion_coeff_zero`.
The positive-coefficient hypothesis extends to index zero without a new input. -/
theorem modular_coefficients_all {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (n : ℕ) : (qExpansion 1 f).coeff n = (E.LFunction n : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [CuspFormClass.qExpansion_coeff_zero f one_pos
      (TauCeti.one_mem_strictPeriods_Gamma0_map N)]
    simp
  · exact hf n hn

/-- **PROVED**, by `lFunction_one`. Locator: the normalization condition in
Li 1975, §2, p. 294. A form with the elliptic curve's positive Dirichlet
coefficients already has first Fourier coefficient one. -/
theorem modular_form_normalized {N : ℕ} (E : WeierstrassCurve ℚ)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) :
    (qExpansion 1 f).coeff 1 = 1 := by
  rw [hf 1 Nat.one_pos, lFunction_one]
  simp

/-- **PROVED**, from the actual local Euler polynomial and the Fourier
coefficient characterization of the Hecke operator; locator:
`HeckeSlash/Nebentypus/Eigenvector.lean`,
`heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul`.
Restriction to the trivial-character space preserves the function. -/
theorem modular_restrict_hecke_good {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) :
    heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩)
        ((TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) =
      (E.LFunction p : ℂ) •
        ((TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) := by
  apply (heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul hp hpN
    ((TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f).2 (E.LFunction p : ℂ)).mpr
  intro m
  rw [coe_restrict_trivial]
  simp only [modular_coefficients_all E f hf, MonoidHom.one_apply, Units.val_one,
    one_mul, show (2 : ℤ) - 1 = 1 by omega, zpow_one]
  have h := lFunction_good_prime_mul E p hp hgood m
  by_cases hpm : p ∣ m
  · simp only [ite_eq_left hpm] at h ⊢
    exact_mod_cast h
  · simp only [ite_eq_right hpm] at h ⊢
    exact_mod_cast h

/-- **PROVED**, by transport through the trivial-character linear equivalence;
locator: `NewformPeriodsDictionary.heckeGamma0`. This is the eigenvector
identity on the genuine space `S₂(Γ₀(N))`, not merely a coefficient identity. -/
theorem modular_heckeGamma0_good {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) :
    heckeGamma0 N p f = (E.LFunction p : ℂ) • f := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul
    hp (modular_restrict_hecke_good E f hf p hp hpN hgood)
  change TauCeti.cuspFormCharSpaceOneEquiv N 2
    (heckeRingHomCuspCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ)
      (heckeTCompositeGamma0 N p)
        ((TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f)) = _
  rw [h, map_smul, LinearEquiv.apply_symm_apply]

/-- **PROVED**, from good reduction at almost all rational primes; locator:
`NewformPeriodsDictionary.goodReductionAt_almost_all_primes`.
This closes the arithmetic Hecke bridge without assuming that the supplied
level contains every prime of bad reduction. -/
theorem modular_hecke_almost_all {N : ℕ} [NeZero N] (E : WeierstrassCurve ℚ)
    (hE : E.IsElliptic)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) :
    (qExpansion 1 f).coeff 1 = 1 ∧
      ∃ S : Finset ℕ, ∀ (p : ℕ) (_hp : p.Prime), Nat.Coprime p N → p ∉ S →
        heckeGamma0 N p f = (E.LFunction p : ℂ) • f := by
  obtain ⟨S, hS⟩ := goodReductionAt_almost_all_primes E hE
  exact ⟨modular_form_normalized E f hf, S,
    fun p hp hpN hpS => modular_heckeGamma0_good E f hf p hp hpN (hS p hp hpS)⟩

/-- **PROVED**, by the old/new decomposition with a finite exceptional set.
Locators: Li 1975, §2, p. 294, Theorem 3, p. 295; the proved spanning theorem
`Newform.span_levelRaise_eq_top` in `Newforms/Decomposition.lean`.
A nonzero good-prime eigenvector outside a finite set has the eigensystem
of a divisor-level newform outside the same set, with the inducing character. -/
theorem exists_newform_of_cofinite_prime_eigen {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hFχ : F ∈ cuspFormCharSpace k χ) (hF0 : F ≠ 0)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (hF : ∀ (p : ℕ) (hp : p.Prime), Nat.Coprime p N → p ∉ S →
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = a p • F) :
    ∃ (M : ℕ) (_ : NeZero M) (hMN : M ∣ N) (g : Newform M k),
      g.χ.comp (ZMod.unitsMap hMN) = χ ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N), p ∉ S →
        g.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN) = a p := by
  classical
  let I := {p : ℕ // p.Prime ∧ Nat.Coprime p N ∧ p ∉ S}
  let T : I → Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    fun p => heckeTCuspNat k p.1 (_hn := ⟨p.2.1.ne_zero⟩)
  let V : (I → ℂ) → Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    fun b => Submodule.span ℂ {G | ∃ (M d : ℕ) (_ : NeZero M) (_ : NeZero d)
      (h : d * M ∣ N) (g : Newform M k),
      (∀ p : I, g.eigenvalue ⟨p.1, p.2.1.pos⟩
        (p.2.2.1.coprime_dvd_right (dvd_of_mul_left_dvd h)) = b p) ∧
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g.toCuspForm = G}
  have hV : ∀ b, V b ≤ ⨅ p, (T p).eigenspace (b p) := by
    intro b
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨M, d, _, _, h, g, hg, rfl⟩
    refine Submodule.mem_iInf _ |>.mpr fun p => Module.End.mem_eigenspace_iff.mpr ?_
    simp only [T]
    rw [g.heckeTCuspNat_levelRaise_eq_eigenvalue_smul h p.2.1 p.2.2.1, hg p]
  have htop : ⨆ b, V b = ⊤ := by
    refine eq_top_iff.mpr ((Newform.span_levelRaise_eq_top N k).ge.trans
      (Submodule.span_le.mpr ?_))
    rintro _ ⟨M, d, _, _, h, g, rfl⟩
    exact Submodule.mem_iSup_of_mem
      (fun p : I => g.eigenvalue ⟨p.1, p.2.1.pos⟩
        (p.2.2.1.coprime_dvd_right (dvd_of_mul_left_dvd h)))
      (Submodule.subset_span ⟨M, d, inferInstance, inferInstance, h, g,
        fun _ => rfl, rfl⟩)
  let b : I → ℂ := fun p => a p.1
  have hmem : F ∈ ⨆ c, V c := htop ▸ Submodule.mem_top
  rw [iSup_split_single V b] at hmem
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hmem
  have hFeig : F ∈ ⨅ p, (T p).eigenspace (b p) :=
    Submodule.mem_iInf _ |>.mpr fun p => Module.End.mem_eigenspace_iff.mpr
      (hF p.1 p.2.1 p.2.2.1 p.2.2.2)
  have hteig : t ∈ ⨅ p, (T p).eigenspace (b p) := by
    have := Submodule.sub_mem _ hFeig (hV b hs)
    rwa [← hst, add_sub_cancel_left] at this
  have ht0 : t = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_iInf_eigenspace T b)) t hteig
      (iSup₂_mono (fun c _ => hV c) ht)
  have hFmem : F ∈ V b := by
    rw [ht0, add_zero] at hst
    exact hst ▸ hs
  by_contra hne
  refine hF0 ((Submodule.disjoint_def.mp
    (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ)) F hFχ
      (Submodule.span_le.mpr ?_ hFmem))
  rintro _ ⟨M, d, _, _, hdM, g, hg, rfl⟩
  have hMN : M ∣ N := dvd_of_mul_left_dvd hdM
  have hgχ : g.χ.comp (ZMod.unitsMap hMN) ≠ χ := by
    intro hc
    apply hne
    exact ⟨M, inferInstance, hMN, g, hc,
      fun p hp hpN hpS => hg ⟨p, hp, hpN, hpS⟩⟩
  exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
    (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace))

/-- **PROVED**, by the arithmetic Hecke bridge and old/new decomposition.
Locators: Li 1975, §2, p. 294, Theorem 3, p. 295; `exists_newform_of_cofinite_prime_eigen`.
From precisely the modularity data in G0 one obtains a normalized newform
of divisor level and trivial character with the elliptic coefficients at
almost all primes. Bad-prime agreement is not part of this theorem. -/
theorem exists_newform_almost_all_prime_coeff (E : WeierstrassCurve ℚ)
    (hE : E.IsElliptic) (N : ℕ) (hN : 0 < N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) :
    ∃ (M : ℕ) (_ : NeZero M) (g : Newform M 2), M ∣ N ∧ g.χ = 1 ∧
      ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
        (qExpansion 1 g.toCuspForm).coeff p = (E.LFunction p : ℂ) := by
  classical
  have : NeZero N := ⟨hN.ne'⟩
  let F := (TauCeti.cuspFormCharSpaceOneEquiv N 2).symm f
  have hF0 : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) ≠ 0 := by
    intro hz
    have hh : (qExpansion 1 (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)).coeff 1 = 1 := by
      rw [coe_restrict_trivial]
      exact modular_form_normalized E f hf
    rw [hz, FunLike.coe_zero, qExpansion_zero] at hh
    simp at hh
  obtain ⟨S, hS⟩ := goodReductionAt_almost_all_primes E hE
  obtain ⟨M, hM0, hMN, g, hgχ, hg⟩ :=
    exists_newform_of_cofinite_prime_eigen F.2 hF0 S (fun p => (E.LFunction p : ℂ))
      (fun p hp hpN hpS => modular_restrict_hecke_good E f hf p hp hpN (hS p hp hpS))
  have hχ : g.χ = 1 := by
    apply MonoidHom.ext
    intro u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hMN u
    have h := congrArg (fun c : (ZMod N)ˣ →* ℂˣ => c v) hgχ
    simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using h
  refine ⟨M, hM0, g, hMN, hχ, S ∪ N.primeFactors, fun p hp hpS => ?_⟩
  have hpS' : p ∉ S := fun h => hpS (Finset.mem_union_left _ h)
  have hpN : Nat.Coprime p N := hp.coprime_iff_not_dvd.mpr (fun hdiv =>
    hpS (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hN.ne'⟩)))
  exact (g.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue g.isNorm
    ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN)).trans (hg p hp hpN hpS')

/-- **PROVED**, by the divisor-level extraction and the genuine full-eigenform
and trivial-character APIs. Locators: Li 1975, §2, p. 294, Theorem 3(i),
p. 295; `Newform.toEigenform`, `cuspFormCharSpaceOneEquiv`,
`Newform.qExpansion_coeff_one`.
This is G0 with equality at almost all primes rather than at every positive
index; normalization and eigen-ness at every operator, including bad primes,
are already proved at the extracted level. -/
theorem exists_gamma0_full_eigenform_almost_all (E : WeierstrassCurve ℚ)
    (hE : E.IsElliptic) (N : ℕ) (hN : 0 < N)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) :
    ∃ (M : ℕ) (_ : NeZero M)
      (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2), M ∣ N ∧
      ZInQ.Contrib.RC53Assist.NewformPeriods.IsNormalizedFullEigenformGamma0 M g ∧
      ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
        (qExpansion 1 g).coeff p = (E.LFunction p : ℂ) := by
  obtain ⟨M, hM0, F, hMN, hχ, S, hcoeff⟩ :=
    exists_newform_almost_all_prime_coeff E hE N hN f hf
  have hmem : F.toCuspForm ∈ cuspFormCharSpace (N := M) 2 (1 : (ZMod M)ˣ →* ℂˣ) :=
    hχ ▸ F.mem_charSpace
  set g := TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨F.toCuspForm, hmem⟩
  have hg : ⇑g = ⇑F.toCuspForm := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply _
  refine ⟨M, hM0, g, hMN, ⟨?_, F.toEigenform, ?_, fun τ => ?_⟩,
    S, fun p hp hpS => ?_⟩
  · rw [show qExpansion 1 g = qExpansion 1 F.toCuspForm from congrArg (qExpansion 1) hg]
    exact Newform.qExpansion_coeff_one F
  · rw [Newform.toEigenform_χ, hχ]
  · rw [Newform.toEigenform_toCuspForm, hg]
  · rw [show qExpansion 1 g = qExpansion 1 F.toCuspForm from congrArg (qExpansion 1) hg]
    exact hcoeff p hp hpS

/-- **DEFINITION**, the arithmetic function of the genuine Fourier coefficients
of a weight-two newform. Locator: `Newform.toCuspForm`; the coefficient at
zero vanishes by the cusp condition. -/
def newformCoefficients {M : ℕ} [NeZero M] (F : Newform M 2) : ArithmeticFunction ℂ :=
  ⟨fun n => (qExpansion 1 F.toCuspForm).coeff n,
    CuspFormClass.qExpansion_coeff_zero F.toCuspForm one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map M)⟩

/-- **PROVED**, by definition; locator: `newformCoefficients`.
No scalar, normalization, or Fourier coefficient is changed by bundling. -/
theorem newformCoefficients_apply {M : ℕ} [NeZero M] (F : Newform M 2) (n : ℕ) :
    newformCoefficients F n = (qExpansion 1 F.toCuspForm).coeff n := rfl

/-- **PROVED**, from normalization and the full Hecke eigenform recurrence.
Locator: `Eigenform.qExpansion_coeff_mul`, including indices divisible by
the level. The newform coefficient arithmetic function is multiplicative. -/
theorem newformCoefficients_isMultiplicative {M : ℕ} [NeZero M] (F : Newform M 2) :
    (newformCoefficients F).IsMultiplicative := by
  refine ⟨F.isNorm, fun {m n} hmn => ?_⟩
  have h := F.toEigenform.qExpansion_coeff_mul F.toEigenform_qExpansion_coeff_one hmn
  simpa only [newformCoefficients_apply, Newform.toEigenform_toCuspForm] using h

/-- **PROVED**, from the full eigenform API and the trivial-character
zero-extension. Locators: Li 1975, Theorem 3(i), p. 295;
`Eigenform.qExpansion_coeff_prime_pow_add_two`.
The quadratic scalar is `p` off the level and zero at a prime of the level. -/
theorem newform_prime_pow_recurrence {M : ℕ} [NeZero M] (F : Newform M 2)
    (hχ : F.χ = 1) (p : ℕ) (hp : p.Prime) (r : ℕ) :
    (qExpansion 1 F.toCuspForm).coeff (p ^ (r + 2)) =
      (qExpansion 1 F.toCuspForm).coeff p *
        (qExpansion 1 F.toCuspForm).coeff (p ^ (r + 1)) -
      (if Nat.Coprime p M then (p : ℂ) else 0) *
        (qExpansion 1 F.toCuspForm).coeff (p ^ r) := by
  have h := F.toEigenform.qExpansion_coeff_prime_pow_add_two
    F.toEigenform_qExpansion_coeff_one hp r
  simp only [Newform.toEigenform_toCuspForm, Newform.toEigenform_χ] at h
  rw [hχ, unitHom_one_apply M p, show (2 : ℤ) - 1 = 1 by omega, zpow_one] at h
  by_cases hcop : Nat.Coprime p M
  · rw [ite_eq_left hcop] at h ⊢
    simpa only [one_mul] using h
  · rw [ite_eq_right hcop] at h ⊢
    simpa only [zero_mul, sub_zero] using h

/-- **DEFINITION**, the local Euler polynomial read from a weight-two
trivial-character newform. Locator: Li 1975, Theorem 3(i), p. 295.
Its bad-prime quadratic coefficient is zero, not `p`. -/
def newformEulerPolynomial {M : ℕ} [NeZero M] (F : Newform M 2) (_hχ : F.χ = 1)
    (p : ℕ) : ℂ[X] :=
  1 - Polynomial.C ((qExpansion 1 F.toCuspForm).coeff p) * Polynomial.X +
    Polynomial.C (if Nat.Coprime p M then (p : ℂ) else 0) * Polynomial.X ^ 2

/-- **PROVED**, by extracting the linear and quadratic coefficients of a
single local-polynomial equality and applying the two recurrences.
Locators: `lFunction_prime_pow_recurrence`, `newform_prime_pow_recurrence`.
A comparison at one prime gives equality at every power of that prime;
no equality at all primes or existence conclusion is assumed. -/
theorem newform_prime_pow_coeff_of_local_polynomial (E : WeierstrassCurve ℚ)
    {M : ℕ} [NeZero M] (F : Newform M 2) (hχ : F.χ = 1)
    (p : ℕ) (hp : p.Prime)
    (hlocal : (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℂ) =
      newformEulerPolynomial F hχ p) (r : ℕ) :
    (qExpansion 1 F.toCuspForm).coeff (p ^ r) = (E.LFunction (p ^ r) : ℂ) := by
  have h₁ := congrArg (fun P : ℂ[X] => P.coeff 1) hlocal
  have h₂ := congrArg (fun P : ℂ[X] => P.coeff 2) hlocal
  have hlinear : ((localPolynomialQ E (primeIdealQ p hp)).coeff 1 : ℂ) =
      -(qExpansion 1 F.toCuspForm).coeff p := by
    simpa [newformEulerPolynomial, Polynomial.coeff_one] using h₁
  have hquad : ((localPolynomialQ E (primeIdealQ p hp)).coeff 2 : ℂ) =
      if Nat.Coprime p M then (p : ℂ) else 0 := by
    simpa [newformEulerPolynomial, Polynomial.coeff_one] using h₂
  have hprime : (qExpansion 1 F.toCuspForm).coeff p = (E.LFunction p : ℂ) := by
    rw [lFunction_prime_eq_neg_localPolynomial_coeff E p hp, Int.cast_neg, hlinear, neg_neg]
  induction r using Nat.twoStepInduction with
  | zero =>
    rw [pow_zero, F.isNorm, lFunction_one]
    simp
  | one => simpa only [pow_one] using hprime
  | more r ih₁ ih₂ =>
    rw [newform_prime_pow_recurrence F hχ p hp r, hprime, ih₁, ih₂, ← hquad]
    symm
    exact_mod_cast lFunction_prime_pow_recurrence E p hp r

end HeckeBridge

end ZInQ.Contrib.RC53Assist.NewformGlueG0
