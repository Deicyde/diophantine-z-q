import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GenusRootsProof
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalCommon
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Frobenius

/-!
# GenusOdd: the values `χ(𝔭)` entering the local comparison (PROVED)

* `not_dvd_conductor_of_not_dvd`: a prime `𝔭 ∣ p` with `p ∤ c` is prime to the conductor of
  `O_c = ℤ + c𝓞_K` (`c` lies in the conductor);
* `chiAt_eq_zero_of_dvd`: for `K` quadratic and `𝔭 ∣ p ∣ c`, the conductor is contained in `𝔭`
  (a conductor element outside `𝔭` would make `ℤ → 𝓞_K/p𝓞_K` onto, while `N(p𝓞_K) = p²`), so
  CST's `chiAt` vanishes at `𝔭`;
* `chiAt_eq_chiD_partner`: **`χ(𝔭) = χ_{d₂}(N𝔭)`** at every `𝔭` prime to `c` with `2d₂ ∉ 𝔭`. The
  hypothesis `IsQuadRingClassChar K c d₁ χ` only fixes `χ(𝔭) = χ_{d₁}(N𝔭)` for `d₁ ∉ 𝔭`; at a
  ramified `𝔭 ∣ d₁` the value is read off from the action of the Frobenius at `𝔭` on `√d₂ ∈ H_c`:
  it is `χ(𝔭)` by the genus action (`genusRoots_proof`, splitting law) and `(N𝔭 / |d₂|)` by
  Euler's criterion (`frob_smul_sqrt`).
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

variable {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]

/-- `c ∈ f(O_c)` (PROVED). -/
theorem natCast_mem_conductorOrder_conductor :
    ((c : ℤ) : 𝓞 K) ∈ (conductorOrder K c).conductor :=
  ((conductorOrder K c).mem_conductor_iff _).mpr fun y => ⟨0, y, by push_cast; ring⟩

/-- **A prime above `p ∤ c` is prime to the conductor** (PROVED). -/
theorem not_dvd_conductor_of_not_dvd {p : ℕ} (hp : p.Prime) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primesAbove K p) (hpc : ¬ p ∣ c) :
    ¬ 𝔭.asIdeal ∣ (conductorOrder K c).conductor := by
  intro hdvd
  have hc : ((c : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.dvd_iff_le.mp hdvd natCast_mem_conductorOrder_conductor
  have hcop : IsCoprime (p : ℤ) (c : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_natCast_natCast]; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpc)
  obtain ⟨u, w, huw⟩ := hcop
  apply 𝔭.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((u * p + w * c : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
    exact add_mem (Ideal.mul_mem_left _ _ h𝔭) (Ideal.mul_mem_left _ _ hc)
  rwa [huw, Int.cast_one] at h1

/-- `N(p 𝓞_K) = p²` for `K` quadratic (PROVED). -/
theorem natCard_quot_span_prime (hK2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Nat.card (𝓞 K ⧸ Ideal.span {((p : ℤ) : 𝓞 K)}) = p ^ 2 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    ← eq_intCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank, hK2]
  simp

/-- **For `K` quadratic and `p ∣ c`, the conductor of `O_c` lies in every prime above `p`**
(PROVED). -/
theorem conductor_le_of_dvd (hK2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ primesAbove K p) (hpc : p ∣ c) :
    (conductorOrder K c).conductor ≤ 𝔭.asIdeal := by
  intro x hx
  by_contra hx𝔭
  set I : Ideal (𝓞 K) := Ideal.span {((p : ℤ) : 𝓞 K)}
  have hcI : ((c : ℤ) : 𝓞 K) ∈ I := by
    obtain ⟨m, hm⟩ := hpc
    rw [hm, Ideal.mem_span_singleton]
    exact ⟨(m : 𝓞 K), by push_cast; ring⟩
  have hI𝔭 : I ≤ 𝔭.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h𝔭
  have hc𝔭 : ((c : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := hI𝔭 hcI
  -- `x = a + c z`
  have hrep : ∀ y : 𝓞 K, ∃ (a : ℤ) (z : 𝓞 K), x * y = (a : 𝓞 K) + ((c : ℤ) : 𝓞 K) * z := by
    intro y
    obtain ⟨a, z, h⟩ := ((conductorOrder K c).mem_conductor_iff x).mp hx y
    refine ⟨a, z, ?_⟩
    apply RingOfIntegers.ext
    push_cast
    exact h
  obtain ⟨a, z, hxz⟩ := hrep 1
  rw [mul_one] at hxz
  have hpa : ¬ (p : ℤ) ∣ a := by
    rintro ⟨m, rfl⟩
    apply hx𝔭
    rw [hxz]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ hc𝔭)
    rw [Int.cast_mul]
    exact Ideal.mul_mem_right _ _ h𝔭
  obtain ⟨b, t, hbt⟩ : IsCoprime a (p : ℤ) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_comm _ _ ▸
      (Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd
        (Nat.prime_iff_prime_int.mp hp)).mpr hpa))))
  -- `ℤ → 𝓞_K / p` is onto
  have hsurj : ∀ y : 𝓞 K, ∃ n : ℤ, Ideal.Quotient.mk I y = (n : 𝓞 K ⧸ I) := by
    intro y
    obtain ⟨a', z', h'⟩ := hrep y
    refine ⟨b * a', ?_⟩
    rw [← map_intCast (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have hy : y = (b * a + t * p : ℤ) • y := by rw [hbt, one_smul]
    have hp' : ((p : ℤ) : 𝓞 K) ∈ I := Ideal.mem_span_singleton_self _
    have key : y - ((b * a' : ℤ) : 𝓞 K) =
        (b : 𝓞 K) * (((c : ℤ) : 𝓞 K) * (z' - z * y)) + (t : 𝓞 K) * ((p : ℤ) : 𝓞 K) * y := by
      have e1 : x * y = (a : 𝓞 K) * y + ((c : ℤ) : 𝓞 K) * z * y := by rw [hxz]; ring
      have e2 : (a : 𝓞 K) * y = (a' : 𝓞 K) + ((c : ℤ) : 𝓞 K) * (z' - z * y) := by
        rw [← sub_eq_zero]; linear_combination e1.symm.trans h'
      have e3 : y = ((b * a + t * p : ℤ) : 𝓞 K) * y := by rw [hbt, Int.cast_one, one_mul]
      calc y - ((b * a' : ℤ) : 𝓞 K)
          = ((b * a + t * p : ℤ) : 𝓞 K) * y - ((b * a' : ℤ) : 𝓞 K) := by rw [← e3]
        _ = (b : 𝓞 K) * ((a : 𝓞 K) * y) + (t : 𝓞 K) * ((p : ℤ) : 𝓞 K) * y -
              (b : 𝓞 K) * (a' : 𝓞 K) := by push_cast; ring
        _ = _ := by rw [e2]; ring
    rw [key]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hcI))
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hp'))
  -- hence `#(𝓞_K / p) ≤ p`
  have hp0 : 0 < p := hp.pos
  let f : Fin p → 𝓞 K ⧸ I := fun i => ((i : ℕ) : 𝓞 K ⧸ I)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨n, hn⟩ := hsurj y
    refine ⟨⟨(n % p).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_lt_of_pos n (by exact_mod_cast hp0 : (0 : ℤ) < p)
      have h2 := Int.emod_nonneg n (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
      omega
    · simp only [f]
      rw [hn]
      have h2 := Int.emod_nonneg n (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
      have hcast : (((n % p).toNat : ℕ) : 𝓞 K ⧸ I) = ((n % p : ℤ) : 𝓞 K ⧸ I) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]
      rw [hcast, ← map_intCast (Ideal.Quotient.mk I), ← map_intCast (Ideal.Quotient.mk I),
        Ideal.Quotient.eq, ← Int.cast_sub, Ideal.mem_span_singleton]
      have : (p : ℤ) ∣ n % p - n := by
        exact ⟨-(n / p), by rw [Int.emod_def]; ring⟩
      obtain ⟨m, hm⟩ := this
      exact ⟨(m : 𝓞 K), by rw [hm]; push_cast; ring⟩
  have : Finite (𝓞 K ⧸ I) := Finite.of_surjective f hf
  have hle := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin, natCard_quot_span_prime hK2 p] at hle
  have : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

/-- **`χ(𝔭) = 0` at a prime above `p ∣ c`** (PROVED; CST's `chiAt` is `0` off the primes prime to
the conductor). -/
theorem chiAt_eq_zero_of_dvd (hK2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ primesAbove K p) (hpc : p ∣ c)
    (χ : Pic (conductorOrder K c) →* ℂˣ) : chiAt (conductorOrder K c) χ 𝔭 = 0 := by
  unfold chiAt
  rw [dif_neg]
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  rintro ⟨-, htop⟩
  rw [sup_eq_left.mpr (conductor_le_of_dvd hK2 hp h𝔭 hpc)] at htop
  exact 𝔭.isPrime.ne_top htop

/-- `χ(𝔭)` at a prime prime to the conductor is `χ` of the class of `𝔭` (PROVED). -/
theorem chiAt_eq_of_not_dvd {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭c : ¬ 𝔭.asIdeal ∣ (conductorOrder K c).conductor) (χ : Pic (conductorOrder K c) →* ℂˣ) :
    chiAt (conductorOrder K c) χ 𝔭 =
      ((χ ((conductorOrder K c).picClass ⟨𝔭.asIdeal, mem_primeTo_of_not_dvd h𝔭c⟩) : ℂˣ) : ℂ) := by
  unfold chiAt
  rw [dif_pos (mem_primeTo_of_not_dvd h𝔭c)]

/-- **`χ(𝔭) = χ_{d₂}(N𝔭)`** (PROVED) at every prime `𝔭` of `K` prime to `c` with `2 d₂ ∉ 𝔭`, for
`χ = χ_{d₁} ∘ N` on `Pic(O_c)` and `d₁ d₂ = disc(K) c²` (`d₂ ≡ 1 mod 4`). This covers the ramified
primes `𝔭 ∣ d₁`, where `IsQuadRingClassChar` says nothing: the Frobenius at `𝔭` in `Gal(H_c/K)` is
the Artin image of `[𝔭]` and acts on `√d₂ ∈ H_c` by `χ([𝔭])` (genus action) and by `(N𝔭/|d₂|)`
(Euler's criterion). -/
theorem chiAt_eq_chiD_partner (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (hDodd : Odd (discr K)) {d₁ d₂ : ℤ} (hprod : d₁ * d₂ = discr K * c ^ 2) (hd₁ : d₁ % 4 = 1)
    (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁) (hcD : Nat.Coprime c (discr K).natAbs)
    (hd₂ : d₂ % 4 = 1) {χ : Pic (conductorOrder K c) →* ℂˣ} (hχ : IsQuadRingClassChar K c d₁ χ)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭c : ¬ 𝔭.asIdeal ∣ (conductorOrder K c).conductor)
    (h2d : ((2 * d₂ : ℤ) : 𝓞 K) ∉ 𝔭.asIdeal) :
    chiAt (conductorOrder K c) χ 𝔭 = ((chiD d₂ (Ideal.absNorm 𝔭.asIdeal) : ℤ) : ℂ) := by
  obtain ⟨s₁, s₂, -, hs₂, hact⟩ :=
    genusRoots_proof K hK2 hTC hDodd c d₁ d₂ hprod hd₁ hsq hcd hcD χ hχ
  have hchar : CharZero (ringClassField (conductorOrder K c)) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have hd₂0 : d₂ ≠ 0 := by rintro rfl; norm_num at hd₂
  have hs₂0 : s₂ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hs₂
    exact hd₂0 (by exact_mod_cast hs₂.symm)
  -- a prime of `H_c` above `𝔭` and a Frobenius there
  have := 𝔭.isMaximal
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := 𝓞 (ringClassField (conductorOrder K c))) 𝔭.asIdeal (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 (ringClassField (conductorOrder K c))))]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply 𝔭.ne_bot
    rw [← hQ]
    exact Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 (ringClassField (conductorOrder K c))))
  let w : HeightOneSpectrum (𝓞 (ringClassField (conductorOrder K c))) :=
    ⟨Q, hQmax.isPrime, hQ0⟩
  have hlies : w.asIdeal.LiesOver 𝔭.asIdeal := ⟨hQ.symm⟩
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K w.asIdeal hQ0
  have hart := frob_eq_artin h𝔭c w hσ
  -- `√d₂` as an integer of `H_c`
  have hint : IsIntegral ℤ s₂ := IsIntegral.of_pow (n := 2) (by norm_num)
    (by rw [hs₂, ← eq_intCast (algebraMap ℤ (ringClassField (conductorOrder K c))) d₂]
        exact isIntegral_algebraMap)
  set s' : 𝓞 (ringClassField (conductorOrder K c)) := ⟨s₂, hint⟩
  have hs' : s' ^ 2 = (d₂ : 𝓞 (ringClassField (conductorOrder K c))) := by
    apply RingOfIntegers.ext; push_cast; exact hs₂
  have hfrob := frob_smul_sqrt (K := K) (L := ringClassField (conductorOrder K c)) hd₂ s' hs' σ
    w.asIdeal 𝔭.asIdeal h2d hσ
  have hfrob' : σ s₂ = ((jacobiSym (Ideal.absNorm 𝔭.asIdeal) d₂.natAbs : ℤ) :
      ringClassField (conductorOrder K c)) * s₂ := by
    have hτs : σ s₂ = ((σ • s' : 𝓞 (ringClassField (conductorOrder K c))) :
        ringClassField (conductorOrder K c)) := rfl
    rw [hτs, hfrob]
    push_cast
    rfl
  have h2 := (hact σ).2
  have hsign : ((chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) :
      ringClassField (conductorOrder K c)) =
      ((jacobiSym (Ideal.absNorm 𝔭.asIdeal) d₂.natAbs : ℤ) : ringClassField (conductorOrder K c)) :=
    mul_right_cancel₀ hs₂0 (h2.symm.trans hfrob')
  have hsign' : chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) =
      jacobiSym (Ideal.absNorm 𝔭.asIdeal) d₂.natAbs := by exact_mod_cast hsign
  rw [hart, MulEquiv.symm_apply_apply] at hsign'
  rw [chiAt_eq_of_not_dvd h𝔭c, ← chiSign_coe hχ.1, hsign']
  rfl

end ZInQ.Contrib.CloudB3RC53.GenusOdd
