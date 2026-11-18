import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalPoly
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.EulerRegroup
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ChiLocal
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ArtinArith
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Decomp
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Arith
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Dictionary
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Newform

/-!
# GenusOdd: `ArtinFactorization` from the local statement `LocalFactorK` (PROVED reduction)

`artinFactorization_of_local : HasseConvergence → GoodReductionOffLevel → LocalFactorK →
ArtinFactorization`.

Proof. Both `L(E/K, χ, s)` (CST's `twistedLFunction`, an Euler product over the primes of `K`) and
`L(E^{(d₁)}, s) L(E^{(d₂)}, s)` (a Dirichlet convolution of two Euler products over the primes of
`ℚ`) are multiplicative arithmetic functions, so it suffices to compare them at prime powers `p^k`.

* `L(E/K, χ)` at `p^k` only sees the primes `𝔭 ∣ p` (`eulerProduct_apply_prime_pow`), whose factors
  are `1/L_𝔭(χ(𝔭) N𝔭^{-s})` with `N𝔭 = p^f` (`natCard_residueField_adicCompletionIntegers`).
* The twist factors at `p` are `1/L_p(χ_{d_i}(p) p^{-s})` (lane RC18: `localPolynomial_qtwist_of_not_dvd`
  for `p ∤ d_i`, additive reduction `localPolynomial_qtwist_of_dvd` for `p ∣ d_i`, where `E` is good
  by `GoodReductionOffLevel`).
* The decomposition law (`decomposition`) sorts `p` into split / inert / ramified; `LocalFactorK`
  gives `L_𝔭` through `L_p`; the values `χ(𝔭)` are `0` at `𝔭 ∣ c` (`chiAt_eq_zero_of_dvd`),
  `χ_{d₁}(N𝔭)` at `𝔭 ∤ d₁` (`IsQuadRingClassChar`) and `χ_{d₂}(N𝔭)` at the ramified `𝔭 ∣ d₁`
  (`chiAt_eq_chiD_partner`); the local identities of `LocalPoly.lean` then match the factors.
* The `L`-series of the convolution is the product of the `L`-series on `Re s > 3/2`, where both
  converge absolutely (`HasseConvergence`, lane RC8's GLUE: Hasse's bound).
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory ArithmeticFunction Rat.HeightOneSpectrum

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

/-- `1/P` has constant coefficient `1` (PROVED). -/
theorem constantCoeff_invC {P : Polynomial ℤ} : PowerSeries.constantCoeff (invC P) = 1 := by
  rw [invC, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
  simp

/-- `1/P(0·T) = 1` (PROVED). -/
theorem rescale_zero_invC (P : Polynomial ℤ) : PowerSeries.rescale (0 : ℂ) (invC P) = 1 := by
  rw [PowerSeries.rescale_zero_apply, constantCoeff_invC, map_one]

/-- CST's local factor at `𝔭` is `1/L_𝔭(χ(𝔭) T)` (PROVED, definitional). -/
theorem twistFactor_eq {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
    (χv : HeightOneSpectrum (𝓞 K) → ℂ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    twistFactor E χv 𝔭 = PowerSeries.rescale (χv 𝔭) (invC (localPolyK E 𝔭)) := rfl

/-- **The twist factor at `p`** (PROVED, from lane RC18's local twist computations): for
`d ≡ 1 (mod 4)` squarefree, `1/L_p(E^{(d)}, T) = 1/L_p(E, χ_d(p) T)`, with `χ_d(p) = 0` and the
factor `1` at `p ∣ d` (where `E` is assumed good). -/
theorem invC_localPolyQ_qtwist (E : WeierstrassCurve ℚ) [E.IsElliptic] {d : ℤ} (hd4 : d % 4 = 1)
    (hsq : Squarefree d) (v : HeightOneSpectrum (𝓞 ℚ))
    (hgood : (natGenerator v : ℤ) ∣ d → GoodAt E v) :
    invC (localPolyQ (qtwist E d) v) =
      PowerSeries.rescale ((kronecker d (natGenerator v) : ℤ) : ℂ) (invC (localPolyQ E v)) := by
  have hp := prime_natGenerator v
  by_cases hpd : (natGenerator v : ℤ) ∣ d
  · have hd1 : d ≠ 1 := by
      rintro rfl
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hpd)
    have hfund : IsFundamentalDiscriminant d := ⟨hd1, Or.inl ⟨hd4, hsq⟩⟩
    rw [localPolyQ, ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_qtwist_of_dvd v E hfund hpd
      (hgood hpd), ZInQ.Manuscript.RC.PrintsAnalytic.kronecker_eq_zero_of_dvd hp hpd, Int.cast_zero,
      rescale_zero_invC, invC_one]
  · have h4 : natGenerator v = 2 → d % 4 = 1 := fun _ => hd4
    rw [localPolyQ, ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_qtwist_of_not_dvd v E hpd h4]
    exact invC_comp_C_mul_X (ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_coeff_zero _) _

/-- An integer lies in a prime above `p` iff `p` divides it (PROVED). -/
theorem intCast_mem_iff {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ primesAbove K p) (n : ℤ) :
    ((n : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal ↔ (p : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hpn
    obtain ⟨u, w, huw⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hpn
    apply 𝔭.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : ((u * p + w * n : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
      exact add_mem (Ideal.mul_mem_left _ _ h𝔭) (Ideal.mul_mem_left _ _ hn)
    rwa [huw, Int.cast_one] at h1
  · rintro ⟨m, rfl⟩
    rw [Int.cast_mul]
    exact Ideal.mul_mem_right _ _ h𝔭

/-- A prime dividing `d₁ d₂` does not divide a level prime to `d₁ d₂` (PROVED). -/
theorem not_dvd_level_of_dvd' {d₁ d₂ : ℤ} {N p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime (d₁ * d₂).natAbs N) (hpd : (p : ℤ) ∣ d₁ * d₂) : ¬ p ∣ N := by
  intro hpN
  have h1 : p ∣ (d₁ * d₂).natAbs := Int.natCast_dvd.mp hpd
  have := Nat.dvd_gcd h1 hpN
  rw [hcop] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

open Classical in
/-- The finite set of primes above `p` from a two-element description (PROVED). -/
theorem primesAboveFinset_eq_pair {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0)
    {𝔭 𝔮 : HeightOneSpectrum (𝓞 K)} (h : primesAbove K p = {𝔭, 𝔮}) :
    primesAboveFinset K p hp = {𝔭, 𝔮} := by
  apply Finset.coe_injective
  rw [primesAboveFinset, Set.Finite.coe_toFinset, h, Finset.coe_pair]

open Classical in
/-- The finite set of primes above `p` from a one-element description (PROVED). -/
theorem primesAboveFinset_eq_singleton {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h : primesAbove K p = {𝔭}) :
    primesAboveFinset K p hp = {𝔭} := by
  apply Finset.coe_injective
  rw [primesAboveFinset, Set.Finite.coe_toFinset, h, Finset.coe_singleton]

open Classical in
/-- **The Euler factor of `L(E/K, χ)` at `p` is that of `L(E^{(d₁)}) L(E^{(d₂)})`** (PROVED from
`GoodReductionOffLevel` and `LocalFactorK`): the product over the primes `𝔭 ∣ p` of the twisted
local factors of `E/K` equals, as arithmetic functions supported on powers of `p`,
`1/L_p(E^{(d₁)}) · 1/L_p(E^{(d₂)})`. -/
theorem prod_twistFactor_eq (hG : GoodReductionOffLevel) (hL : LocalFactorK)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hDodd : Odd (discr K))
    (c : ℕ) [NeZero c] (d₁ d₂ : ℤ) (hprod : d₁ * d₂ = discr K * c ^ 2) (hd₁ : d₁ % 4 = 1)
    (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁) (hcD : Nat.Coprime c (discr K).natAbs)
    (hlev : Nat.Coprime (d₁ * d₂).natAbs (newformLevel E))
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hχ : IsQuadRingClassChar K c d₁ χ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∏ 𝔭 ∈ primesAboveFinset K (natGenerator v) (prime_natGenerator v).ne_zero,
        ofPowerSeries (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)))
          (twistFactor E (chiAt (conductorOrder K c) χ) 𝔭) =
      ofPowerSeries (natGenerator v)
        (invC (localPolyQ (qtwist E d₁) v) * invC (localPolyQ (qtwist E d₂) v)) := by
  have hp : (natGenerator v).Prime := prime_natGenerator v
  have hD4 := discr_mod_four_of_odd hK2 hDodd
  have hDsq := squarefree_discr_of_odd hK2 hDodd
  have hd₂4 := d₂_mod_four hprod hd₁ hD4 hcd
  have hd₂sq := squarefree_d₂ hprod hsq hcd hcD hDsq (NeZero.ne c)
  have hd₁0 : d₁ ≠ 0 := hsq.ne_zero
  have hd₂0 : d₂ ≠ 0 := hd₂sq.ne_zero
  have hD0 : discr K ≠ 0 := hDsq.ne_zero
  have hgood : (natGenerator v : ℤ) ∣ d₁ * d₂ → GoodAt E v := fun h =>
    hG E v (not_dvd_level_of_dvd' hp hlev h)
  rw [invC_localPolyQ_qtwist E hd₁ hsq v (fun h => hgood (Dvd.dvd.mul_right h _)),
    invC_localPolyQ_qtwist E hd₂4 hd₂sq v (fun h => hgood (Dvd.dvd.mul_left h _))]
  set p := natGenerator v with hpdef
  have hF : (localPolyQ E v).coeff 0 = 1 :=
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_coeff_zero _
  have hκ₁ : kronecker d₁ p = chiD d₁ p := (chiD_eq_kronecker hd₁ hp).symm
  have hκ₂ : kronecker d₂ p = chiD d₂ p := (chiD_eq_kronecker hd₂4 hp).symm
  have hκD : kronecker (discr K) p = chiD (discr K) p := (chiD_eq_kronecker hD4 hp).symm
  -- `χ(𝔭) = χ_{d₁}(N𝔭)` away from `c d₁`
  have hval : ∀ 𝔯 ∈ primesAbove K p, ¬ p ∣ c → ¬ (p : ℤ) ∣ d₁ →
      chiAt (conductorOrder K c) χ 𝔯 = (chiD d₁ (Ideal.absNorm 𝔯.asIdeal) : ℂ) := by
    intro 𝔯 h𝔯 hpc hpd
    rw [chiAt_eq_of_not_dvd (not_dvd_conductor_of_not_dvd hp h𝔯 hpc)]
    exact hχ.2 𝔯 _ (fun h => hpd ((intCast_mem_iff hp h𝔯 d₁).mp h))
  have hsubst1 : (1 : PowerSeries ℂ).subst (PowerSeries.X ^ 2 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X_pow two_ne_zero), map_one]
  rcases decomposition hK2 hDodd hp with
      ⟨𝔭, 𝔮, hne, hS, hN𝔭, hN𝔮, hu𝔭, hu𝔮, hkr⟩ | ⟨𝔭, hS, hN, hu, hkr⟩ | ⟨𝔭, hS, hN, hu, hpD⟩
  · -- split
    have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hS]; simp
    have h𝔮 : 𝔮 ∈ primesAbove K p := by rw [hS]; simp
    rw [primesAboveFinset_eq_pair _ hS, Finset.prod_pair hne,
      natCard_residueField_adicCompletionIntegers, natCard_residueField_adicCompletionIntegers,
      hN𝔭, hN𝔮, ← map_mul]
    congr 1
    rw [twistFactor_eq, twistFactor_eq, (hL E K 𝔭 v h𝔭).1 hN𝔭 hu𝔭, (hL E K 𝔮 v h𝔮).1 hN𝔮 hu𝔮]
    by_cases hpc : p ∣ c
    · obtain ⟨h1, h2⟩ := dvd_both_of_dvd_c hprod hsq hcd (NeZero.ne c) hp hpc
      rw [chiAt_eq_zero_of_dvd hK2 hp h𝔭 hpc, chiAt_eq_zero_of_dvd hK2 hp h𝔮 hpc,
        kronecker_eq_zero_of_dvd hp h1, kronecker_eq_zero_of_dvd hp h2, Int.cast_zero]
    · have hpD : ¬ (p : ℤ) ∣ discr K := fun h => by
        rw [kronecker_eq_zero_of_dvd hp h] at hkr; exact absurd hkr (by norm_num)
      have hp1 : ¬ (p : ℤ) ∣ d₁ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inl h))
      have hp2 : ¬ (p : ℤ) ∣ d₂ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inr h))
      have hmul := chiD_mul_chiD hprod hd₁0 hd₂0 hD0 hp hpc
      rw [← hκD, hkr] at hmul
      have h12 : chiD d₂ p = chiD d₁ p := by
        rcases chiD_eq_one_or hp hp1 with h | h <;> rw [h] at hmul ⊢ <;> linarith
      rw [hval 𝔭 h𝔭 hpc hp1, hval 𝔮 h𝔮 hpc hp1, hN𝔭, hN𝔮, hκ₁, hκ₂, h12]
  · -- inert
    have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hS]; simp
    rw [primesAboveFinset_eq_singleton _ hS, Finset.prod_singleton,
      natCard_residueField_adicCompletionIntegers, hN, ofPowerSeries_pow p two_ne_zero]
    congr 1
    rw [twistFactor_eq]
    by_cases hpc : p ∣ c
    · obtain ⟨h1, h2⟩ := dvd_both_of_dvd_c hprod hsq hcd (NeZero.ne c) hp hpc
      rw [chiAt_eq_zero_of_dvd hK2 hp h𝔭 hpc, kronecker_eq_zero_of_dvd hp h1,
        kronecker_eq_zero_of_dvd hp h2, Int.cast_zero, rescale_zero_invC, rescale_zero_invC,
        hsubst1, mul_one]
    · have hpD : ¬ (p : ℤ) ∣ discr K := fun h => by
        rw [kronecker_eq_zero_of_dvd hp h] at hkr; exact absurd hkr (by norm_num)
      have hp1 : ¬ (p : ℤ) ∣ d₁ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inl h))
      have hp2 : ¬ (p : ℤ) ∣ d₂ := fun h => hpD ((dvd_one_iff hprod hp hpc).mp (Or.inr h))
      have hmul := chiD_mul_chiD hprod hd₁0 hd₂0 hD0 hp hpc
      rw [← hκD, hkr] at hmul
      have hε : (kronecker d₁ p = 1 ∧ kronecker d₂ p = -1) ∨
          (kronecker d₁ p = -1 ∧ kronecker d₂ p = 1) := by
        rw [hκ₁, hκ₂]
        rcases chiD_eq_one_or hp hp1 with h | h <;> rw [h] at hmul ⊢
        · left; exact ⟨rfl, by linarith⟩
        · right; exact ⟨rfl, by linarith⟩
      rw [hval 𝔭 h𝔭 hpc hp1, hN, chiD_sq_prime hp hp1, Int.cast_one, PowerSeries.rescale_one,
        RingHom.id_apply]
      exact localIdentity_inert hF ((hL E K 𝔭 v h𝔭).2.2 hN hu) hε
  · -- ramified
    have h𝔭 : 𝔭 ∈ primesAbove K p := by rw [hS]; simp
    have hpc : ¬ p ∣ c := by
      intro hpc
      have h1 : p ∣ Nat.gcd c (discr K).natAbs := Nat.dvd_gcd hpc (Int.natCast_dvd.mp hpD)
      rw [hcD] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hone := (dvd_one_iff hprod hp hpc).mpr hpD
    have hgoodv : GoodAt E v := hgood (by
      rcases hone with h | h
      · exact Dvd.dvd.mul_right h _
      · exact Dvd.dvd.mul_left h _)
    rw [primesAboveFinset_eq_singleton _ hS, Finset.prod_singleton,
      natCard_residueField_adicCompletionIntegers, hN]
    congr 1
    rw [twistFactor_eq, (hL E K 𝔭 v h𝔭).2.1 hN hgoodv]
    have hp2odd : p ≠ 2 := by
      rintro h2
      rw [h2] at hpD
      exact (Int.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr (by exact_mod_cast hpD))
    by_cases hp1 : (p : ℤ) ∣ d₁
    · have hp2 : ¬ (p : ℤ) ∣ d₂ := fun h => not_dvd_both hprod hDsq hp hpc ⟨hp1, h⟩
      have h2d : ((2 * d₂ : ℤ) : 𝓞 K) ∉ 𝔭.asIdeal := by
        rw [intCast_mem_iff hp h𝔭]
        intro h
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
        · have : p ∣ 2 := by exact_mod_cast h
          exact hp2odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
        · exact hp2 h
      rw [chiAt_eq_chiD_partner hK2 hTC hDodd hprod hd₁ hsq hcd hcD hd₂4 hχ
        (not_dvd_conductor_of_not_dvd hp h𝔭 hpc) h2d, hN, kronecker_eq_zero_of_dvd hp hp1,
        Int.cast_zero, rescale_zero_invC, one_mul, hκ₂]
    · have hp2 : (p : ℤ) ∣ d₂ := hone.resolve_left hp1
      rw [hval 𝔭 h𝔭 hpc hp1, hN, kronecker_eq_zero_of_dvd hp hp2, Int.cast_zero,
        rescale_zero_invC, mul_one, hκ₁]

/-- **`ArtinFactorization` from the local statement** (PROVED reduction): the Artin factorization
`L(E/K, χ_{d₁} ∘ N, s) = L(E^{(d₁)}, s) L(E^{(d₂)}, s)` on `Re s > 3/2` follows from
`LocalFactorK` (the Euler factor of `E/K` at each prime of `K` by splitting type),
`GoodReductionOffLevel` (good reduction at the primes not dividing the level) and lane RC8's
`HasseConvergence` (absolute convergence on `Re s > 3/2`). -/
theorem artinFactorization_of_local (hH : HasseConvergence) (hG : GoodReductionOffLevel)
    (hL : LocalFactorK) : ArtinFactorization := by
  intro E _ K _ _ hK2 hTC hDodd _hlevelSplit c _ d₁ d₂ hprod hd₁ hsq hcd hcD hlev χ hχ s hs
  have hD4 := discr_mod_four_of_odd hK2 hDodd
  have hDsq := squarefree_discr_of_odd hK2 hDodd
  have hd₂sq := squarefree_d₂ hprod hsq hcd hcD hDsq (NeZero.ne c)
  have hd₁0 : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hsq.ne_zero
  have hd₂0 : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂sq.ne_zero
  set A₁ : ArithmeticFunction ℂ := ((qtwist E d₁).LFunction : ArithmeticFunction ℂ)
  set A₂ : ArithmeticFunction ℂ := ((qtwist E d₂).LFunction : ArithmeticFunction ℂ)
  -- the identity of arithmetic functions
  have key : twistedLFunction E (chiAt (conductorOrder K c) χ) = A₁ * A₂ := by
    have hmulL : (twistedLFunction E (chiAt (conductorOrder K c) χ)).IsMultiplicative := by
      rw [twistedLFunction_eq_eulerProduct]
      exact isMultiplicative_eulerProduct_ofPowerSeries _ (constantCoeff_twistFactor E _)
    have hmulR : (A₁ * A₂).IsMultiplicative :=
      (ZInQ.Literature.isMultiplicative_LFunction _).intCast.mul
        (ZInQ.Literature.isMultiplicative_LFunction _).intCast
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hmulL _ hmulR).mpr fun p k hp => ?_
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨v, rfl⟩ := ZInQ.Literature.exists_natGenerator_eq p
    rw [twistedLFunction_eq_eulerProduct,
      eulerProduct_apply_prime_pow _ (constantCoeff_twistFactor E _) hp k,
      prod_twistFactor_eq hG hL E K hK2 hTC hDodd c d₁ d₂ hprod hd₁ hsq hcd hcD hlev χ hχ v,
      ofPowerSeries_apply_pow hp.one_lt]
    have hA : ∀ (d : ℤ) (j : ℕ), ((qtwist E d).LFunction : ArithmeticFunction ℂ)
        (natGenerator v ^ j) =
        ofPowerSeries (natGenerator v) (invC (localPolyQ (qtwist E d) v)) (natGenerator v ^ j) := by
      intro d j
      rw [intCoe_apply, ofPowerSeries_apply_pow hp.one_lt, invC, PowerSeries.coeff_map,
        ZInQ.Manuscript.RC.TwistDictionary.LFunction_prime_pow]
      rfl
    rw [mul_apply_prime_pow_congr hp (fun j _ => hA d₁ j) (fun j _ => hA d₂ j), ← map_mul,
      ofPowerSeries_apply_pow hp.one_lt]
  -- `L`-series
  have hsum : ∀ d : ℤ, (d : ℚ) ≠ 0 →
      LSeriesSummable (⇑((qtwist E d).LFunction : ArithmeticFunction ℂ)) s := by
    intro d hd
    have := hH (qtwist E d) (qtwist_isElliptic E hd) s hs
    convert this using 1
    funext n
    rw [intCoe_apply]
    rfl
  rw [key, LSeries_mul' (hsum d₁ hd₁0) (hsum d₂ hd₂0)]
  rfl

end ZInQ.Contrib.CloudB3RC53.GenusOdd
