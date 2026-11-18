import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.EulerRegroup

/-!
# GenusOdd: rational numbers in the completion `K_𝔭` (PROVED)

For a number field `K`, a prime `p` and a prime `𝔭 ∣ p` of `K`, and any ring homomorphism
`ι : ℚ → K_𝔭` (there is only one, `RingHom.ext_rat`):

* (P1) `iota_mem_integers_iff`: `ι x ∈ 𝓞_𝔭 ↔ p ∤ den x`;
* (P2) `valued_iota_eq_one_iff`, `iota_unit_iff`: `ι x` is a unit of `𝓞_𝔭` iff `v_p(x) = 0`
  (any ramification);
* (P3) `charP_residueField`, `natCard_residueField'`, `finite_residueField`: the residue field of
  `𝓞_𝔭` has characteristic `p` and `N𝔭` elements;
* (P4) `exists_sub_mem_integers`: `K_𝔭 = K + 𝓞_𝔭` (density of `K`);
* (P5) `exists_rat_sub_mem_integers`: if `N𝔭 = p` and `𝔭² ∤ p` then `K_𝔭 = ℚ + 𝓞_𝔭`
  (`ℤ → 𝓞_K/𝔭ⁿ` is onto, as `#(𝓞_K/𝔭ⁿ) = pⁿ` and `𝔭ⁿ ∩ ℤ = pⁿℤ`);
* (P6) `exists_rat_associated`: if `𝔭² ∤ p`, every `x ≠ 0` of `K_𝔭` is `ι q` times a unit, `q ∈ ℚ`
  (a power of `p`, `v_𝔭(p) = 1`);
* (P7) `mem_primesAbove_rat`, `absNorm_rat`, `unramifiedOver_rat`: the place `v` of `ℚ` is a prime
  above `natGenerator v` of norm `natGenerator v`, unramified, so (P1)–(P6) apply to `ℚ_v`.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {𝔭 : HeightOneSpectrum (𝓞 K)}

/-! ### Integers and the valuation of `𝔭` -/

/-- An integer lies in a prime above `p` iff `p` divides it (PROVED). -/
theorem intCast_mem_asIdeal_iff (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (n : ℤ) :
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

/-- `v_𝔭(n) < 1` iff `p ∣ n` (PROVED). -/
theorem intValuation_intCast_lt_one_iff (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (n : ℤ) :
    𝔭.intValuation ((n : ℤ) : 𝓞 K) < 1 ↔ (p : ℤ) ∣ n := by
  rw [intValuation_lt_one_iff_mem, intCast_mem_asIdeal_iff hp h𝔭]

/-- `v_𝔭(n) = 1` iff `p ∤ n` (PROVED). -/
theorem intValuation_intCast_eq_one_iff (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (n : ℤ) :
    𝔭.intValuation ((n : ℤ) : 𝓞 K) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  rw [← intValuation_intCast_lt_one_iff hp h𝔭]
  have h := 𝔭.intValuation_le_one ((n : ℤ) : 𝓞 K)
  constructor
  · intro h1; rw [h1]; exact lt_irrefl _
  · intro h1; exact le_antisymm h (not_lt.mp h1)

/-- `v_𝔭(x) = v_𝔭(num x) / v_𝔭(den x)` for `x ∈ ℚ` (PROVED). -/
theorem valuation_ratCast (x : ℚ) :
    𝔭.valuation K (x : K) =
      𝔭.intValuation ((x.num : ℤ) : 𝓞 K) / 𝔭.intValuation (((x.den : ℤ) : ℤ) : 𝓞 K) := by
  have h : (x : K) = algebraMap (𝓞 K) K ((x.num : ℤ) : 𝓞 K) /
      algebraMap (𝓞 K) K (((x.den : ℤ) : ℤ) : 𝓞 K) := by
    rw [map_intCast, map_intCast]
    push_cast
    exact Rat.cast_def x
  rw [h, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap]

/-- Every ring homomorphism `ℚ → K_𝔭` is the composite `ℚ → K → K_𝔭` (PROVED). -/
theorem iota_eq (ι : ℚ →+* 𝔭.adicCompletion K) (x : ℚ) :
    ι x = ((x : K) : 𝔭.adicCompletion K) := by
  have h : ι = (algebraMap K (𝔭.adicCompletion K)).comp (algebraMap ℚ K) := RingHom.ext_rat _ _
  rw [h, RingHom.comp_apply, eq_ratCast]
  rfl

/-- The valuation of `ι x` is that of `x` in `K` (PROVED). -/
theorem valued_iota (ι : ℚ →+* 𝔭.adicCompletion K) (x : ℚ) :
    Valued.v (ι x) = 𝔭.valuation K (x : K) := by
  rw [iota_eq]
  exact valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := 𝔭) (x : K)

theorem intValuation_den_ne_zero (x : ℚ) :
    𝔭.intValuation (((x.den : ℤ) : ℤ) : 𝓞 K) ≠ 0 := by
  apply intValuation_ne_zero
  exact_mod_cast x.den_ne_zero

theorem not_dvd_num_of_dvd_den (hp : p.Prime) {x : ℚ} (h : (p : ℤ) ∣ x.den) :
    ¬ (p : ℤ) ∣ x.num := by
  intro hn
  have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp hn
  have h2 : p ∣ x.den := by exact_mod_cast h
  have := Nat.dvd_gcd h1 h2
  rw [x.reduced] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **(P1)** `ι x ∈ 𝓞_𝔭 ↔ p ∤ den x` (PROVED). -/
theorem iota_mem_integers_iff (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (ι : ℚ →+* 𝔭.adicCompletion K) (x : ℚ) :
    ι x ∈ 𝔭.adicCompletionIntegers K ↔ ¬ (p : ℤ) ∣ x.den := by
  rw [mem_adicCompletionIntegers, valued_iota, valuation_ratCast]
  have hd0 := intValuation_den_ne_zero (𝔭 := 𝔭) x
  rw [div_le_one₀ (zero_lt_iff.mpr hd0)]
  by_cases hd : (p : ℤ) ∣ x.den
  · have hn := not_dvd_num_of_dvd_den hp hd
    rw [(intValuation_intCast_eq_one_iff hp h𝔭 _).mpr hn]
    have := (intValuation_intCast_lt_one_iff hp h𝔭 (x.den : ℤ)).mpr hd
    simp only [hd, not_true_eq_false, iff_false, not_le]
    exact this
  · rw [(intValuation_intCast_eq_one_iff hp h𝔭 (x.den : ℤ)).mpr hd]
    simp only [hd, not_false_eq_true, iff_true]
    exact 𝔭.intValuation_le_one _

/-- **(P2)** `v(ι x) = 1 ↔ v_p(x) = 0` (PROVED). -/
theorem valued_iota_eq_one_iff (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (ι : ℚ →+* 𝔭.adicCompletion K) (x : ℚ) :
    Valued.v (ι x) = 1 ↔ ¬ (p : ℤ) ∣ x.num ∧ ¬ (p : ℤ) ∣ x.den := by
  rw [valued_iota, valuation_ratCast]
  have hd0 := intValuation_den_ne_zero (𝔭 := 𝔭) x
  rw [div_eq_one_iff_eq hd0]
  by_cases hd : (p : ℤ) ∣ x.den
  · have hn := not_dvd_num_of_dvd_den hp hd
    rw [(intValuation_intCast_eq_one_iff hp h𝔭 _).mpr hn]
    have := (intValuation_intCast_lt_one_iff hp h𝔭 (x.den : ℤ)).mpr hd
    simp only [hd, not_true_eq_false, and_false, iff_false]
    exact this.ne'
  · rw [(intValuation_intCast_eq_one_iff hp h𝔭 (x.den : ℤ)).mpr hd,
      intValuation_intCast_eq_one_iff hp h𝔭]
    simp [hd]

/-- In a valued field, `y ≠ 0` is a unit of the integers iff `v(y) = 1` (PROVED). -/
theorem mem_and_inv_mem_iff (y : 𝔭.adicCompletion K) (hy : y ≠ 0) :
    (y ∈ 𝔭.adicCompletionIntegers K ∧ y⁻¹ ∈ 𝔭.adicCompletionIntegers K) ↔ Valued.v y = 1 := by
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, map_inv₀]
  have h0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)
  · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩

/-- **(P2')** `ι x` is a nonzero element with `ι x, (ι x)⁻¹ ∈ 𝓞_𝔭` iff `v_p(x) = 0` (PROVED). -/
theorem iota_unit_iff (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (ι : ℚ →+* 𝔭.adicCompletion K) (x : ℚ) :
    (ι x ≠ 0 ∧ ι x ∈ 𝔭.adicCompletionIntegers K ∧ (ι x)⁻¹ ∈ 𝔭.adicCompletionIntegers K) ↔
      (¬ (p : ℤ) ∣ x.num ∧ ¬ (p : ℤ) ∣ x.den) := by
  rw [← valued_iota_eq_one_iff hp h𝔭 ι]
  constructor
  · rintro ⟨h0, h⟩
    exact (mem_and_inv_mem_iff _ h0).mp h
  · intro h
    have h0 : ι x ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero] at h; exact zero_ne_one h
    exact ⟨h0, (mem_and_inv_mem_iff _ h0).mpr h⟩

/-! ### The residue field -/

/-- **(P3)** The residue field of `𝓞_𝔭` has characteristic `p` (PROVED). -/
theorem charP_residueField (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) :
    CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p := by
  rw [CharP.charP_iff_prime_eq_zero hp]
  set ι : ℚ →+* 𝔭.adicCompletion K := algebraMap ℚ (𝔭.adicCompletion K)
  have hmem : ι (p : ℚ) ∈ 𝔭.adicCompletionIntegers K :=
    (iota_mem_integers_iff hp h𝔭 ι _).mpr (by
      rw [show ((p : ℚ)).den = 1 from rfl]; exact_mod_cast hp.not_dvd_one)
  have hlt : Valued.v (ι (p : ℚ)) ≠ 1 := by
    rw [Ne, valued_iota_eq_one_iff hp h𝔭 ι]
    rintro ⟨h, -⟩
    exact h (by rw [show ((p : ℚ)).num = p from rfl])
  have hcast : ((p : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = ι (p : ℚ) := by
    simp [ι]
  rw [← map_natCast (IsLocalRing.residue (𝔭.adicCompletionIntegers K)),
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one, hcast]
  exact hlt

/-- **(P3)** `#(residue field of 𝓞_𝔭) = N𝔭` (PROVED). -/
theorem natCard_residueField' :
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) = Ideal.absNorm 𝔭.asIdeal :=
  natCard_residueField_adicCompletionIntegers 𝔭

/-- **(P3)** The residue field of `𝓞_𝔭` is finite (PROVED). -/
theorem finite_residueField :
    Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_residueField']
  exact (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
    (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot) |> fun h => h

/-! ### Density -/

/-- **(P4)** `K_𝔭 = K + 𝓞_𝔭` (PROVED). -/
theorem exists_sub_mem_integers (x : 𝔭.adicCompletion K) :
    ∃ y : K, x - algebraMap K (𝔭.adicCompletion K) y ∈ 𝔭.adicCompletionIntegers K := by
  have hopen : IsOpen {z : 𝔭.adicCompletion K | x - z ∈ 𝔭.adicCompletionIntegers K} := by
    have hO : IsOpen ((𝔭.adicCompletionIntegers K : Set (𝔭.adicCompletion K))) :=
      Valued.isOpen_valuationSubring _
    exact hO.preimage (continuous_const.sub continuous_id)
  obtain ⟨y, hy⟩ := (denseRange_algebraMap (R := 𝓞 K) K 𝔭).exists_mem_open hopen
    ⟨x, by simp only [Set.mem_setOf_eq, sub_self]; exact zero_mem _⟩
  exact ⟨y, hy⟩


/-! ### Unramified primes: `v_𝔭(p) = 1` and approximation by rationals -/

/-- **`v_𝔭(p) = 1`** at an unramified `𝔭 ∣ p`: `intValuation p = exp (-1)` (PROVED). -/
theorem intValuation_prime_eq (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hu : UnramifiedOver 𝔭 p) :
    𝔭.intValuation (((p : ℤ) : 𝓞 K)) = exp (-1 : ℤ) := by
  have hp0 : (((p : ℤ) : 𝓞 K)) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : 𝔭.intValuation (((p : ℤ) : 𝓞 K)) ≤ exp (-((1 : ℕ) : ℤ)) :=
    (intValuation_le_pow_iff_dvd _ _ 1).mpr (by rw [pow_one]; exact Ideal.dvd_span_singleton.mpr h𝔭)
  have h2 : ¬ 𝔭.intValuation (((p : ℤ) : 𝓞 K)) ≤ exp (-((2 : ℕ) : ℤ)) :=
    fun h => hu ((intValuation_le_pow_iff_dvd _ _ 2).mp h)
  rw [intValuation_if_neg _ hp0] at h1 h2 ⊢
  set c := (Associates.mk 𝔭.asIdeal).count (Associates.mk (Ideal.span {((p : ℤ) : 𝓞 K)})).factors
  rw [exp_le_exp] at h1 h2
  have hc1 : 1 ≤ c := by push_cast at h1; omega
  have hc2 : c < 2 := by
    by_contra hc
    exact h2 (by push_cast; omega)
  have : c = 1 := by omega
  rw [this]; rfl

/-- **`𝔭ⁿ ∩ ℤ ⊆ pⁿ ℤ`** at an unramified `𝔭 ∣ p` (PROVED). -/
theorem dvd_of_intCast_mem_pow (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hu : UnramifiedOver 𝔭 p) (N : ℕ) :
    ∀ m : ℤ, ((m : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal ^ N → (p : ℤ) ^ N ∣ m := by
  induction N with
  | zero => intro m _; simp
  | succ N ih =>
    intro m hm
    have hm1 : ((m : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := Ideal.pow_le_self (Nat.succ_ne_zero N) hm
    obtain ⟨m₁, rfl⟩ := (intCast_mem_asIdeal_iff hp h𝔭 m).mp hm1
    rw [← intValuation_le_pow_iff_mem, Int.cast_mul, map_mul,
      intValuation_prime_eq hp h𝔭 hu] at hm
    have hm₁ : 𝔭.intValuation ((m₁ : ℤ) : 𝓞 K) ≤ exp (-(N : ℤ)) := by
      have e1 : 𝔭.intValuation ((m₁ : ℤ) : 𝓞 K) =
          exp (1 : ℤ) * (exp (-1 : ℤ) * 𝔭.intValuation ((m₁ : ℤ) : 𝓞 K)) := by
        rw [← mul_assoc, ← exp_add]; simp
      rw [e1]
      calc exp (1 : ℤ) * (exp (-1 : ℤ) * 𝔭.intValuation ((m₁ : ℤ) : 𝓞 K))
          ≤ exp (1 : ℤ) * exp (-((N + 1 : ℕ) : ℤ)) := mul_le_mul_right hm _
        _ = exp (-(N : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    obtain ⟨k, hk⟩ := ih m₁ ((intValuation_le_pow_iff_mem _ _ _).mp hm₁)
    exact ⟨k, by rw [hk]; ring⟩

/-- **`ℤ → 𝓞_K/𝔭ᴺ` is onto** when `N𝔭 = p` and `𝔭² ∤ p` (PROVED). -/
theorem exists_int_sub_mem_pow (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hN : Ideal.absNorm 𝔭.asIdeal = p) (hu : UnramifiedOver 𝔭 p) (α : 𝓞 K) (N : ℕ) :
    ∃ a : ℤ, α - ((a : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal ^ N := by
  set I := 𝔭.asIdeal ^ N
  have hcard : Nat.card (𝓞 K ⧸ I) = p ^ N := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow, hN]
  have hfin : Finite (𝓞 K ⧸ I) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  let f : Fin (p ^ N) → 𝓞 K ⧸ I := fun i => Ideal.Quotient.mk I ((((i : ℕ) : ℤ)) : 𝓞 K)
  have hinj : Function.Injective f := by
    intro i j hij
    simp only [f] at hij
    rw [Ideal.Quotient.eq, ← Int.cast_sub] at hij
    have hdvd := dvd_of_intCast_mem_pow hp h𝔭 hu N _ hij
    have hlt : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < (p : ℤ) ^ N := by
      have hi := i.2
      have hj := j.2
      have e : ((p ^ N : ℕ) : ℤ) = (p : ℤ) ^ N := by push_cast; rfl
      have hi' : ((i : ℕ) : ℤ) < (p : ℤ) ^ N := by rw [← e]; exact_mod_cast hi
      have hj' : ((j : ℕ) : ℤ) < (p : ℤ) ^ N := by rw [← e]; exact_mod_cast hj
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    exact Fin.ext (by omega)
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  obtain ⟨i, hi⟩ := hbij.2 (Ideal.Quotient.mk I α)
  refine ⟨((i : ℕ) : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hi.symm

/-- Elements of `K` are rational modulo `𝓞_𝔭` when `N𝔭 = p` and `𝔭² ∤ p` (PROVED). -/
theorem exists_rat_sub_valuation_le_one (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hN : Ideal.absNorm 𝔭.asIdeal = p) (hu : UnramifiedOver 𝔭 p) (y : K) :
    ∃ q : ℚ, 𝔭.valuation K (y - (q : K)) ≤ 1 := by
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hβ0 : β ≠ 0 := nonZeroDivisors.ne_zero hβ
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 𝔭.intValuation β = exp (-(k : ℤ)) :=
    ⟨_, intValuation_if_neg _ hβ0⟩
  set N := 2 * k + 1
  obtain ⟨a, ha⟩ := exists_int_sub_mem_pow hp h𝔭 hN hu α N
  obtain ⟨b, hb⟩ := exists_int_sub_mem_pow hp h𝔭 hN hu β N
  set A := algebraMap (𝓞 K) K α
  set B := algebraMap (𝓞 K) K β
  have hA : 𝔭.valuation K (A - (a : K)) ≤ exp (-(N : ℤ)) := by
    rw [show A - (a : K) = algebraMap (𝓞 K) K (α - ((a : ℤ) : 𝓞 K)) by
      rw [map_sub, map_intCast], valuation_of_algebraMap]
    exact (intValuation_le_pow_iff_mem _ _ _).mpr ha
  have hB : 𝔭.valuation K (B - (b : K)) ≤ exp (-(N : ℤ)) := by
    rw [show B - (b : K) = algebraMap (𝓞 K) K (β - ((b : ℤ) : 𝓞 K)) by
      rw [map_sub, map_intCast], valuation_of_algebraMap]
    exact (intValuation_le_pow_iff_mem _ _ _).mpr hb
  have hAle : 𝔭.valuation K A ≤ 1 := valuation_le_one _ _
  have hBv : 𝔭.valuation K B = exp (-(k : ℤ)) := by rw [valuation_of_algebraMap, hk]
  have hNk : exp (-(N : ℤ)) < exp (-(k : ℤ)) := by rw [exp_lt_exp]; omega
  have hb' : 𝔭.valuation K (b : K) = exp (-(k : ℤ)) := by
    have h1 : 𝔭.valuation K ((b : K) - B) < 𝔭.valuation K B := by
      rw [← Valuation.map_neg, neg_sub, hBv]; exact lt_of_le_of_lt hB hNk
    have := Valuation.map_add_eq_of_lt_right _ h1
    rwa [sub_add_cancel, hBv] at this
  have hB0 : B ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hBv; exact exp_ne_zero hBv.symm
  have hb0 : (b : K) ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hb'; exact exp_ne_zero hb'.symm
  refine ⟨(a : ℚ) / b, ?_⟩
  have hq : (((a : ℚ) / b : ℚ) : K) = (a : K) / (b : K) := by push_cast; rfl
  rw [hq, div_sub_div _ _ hB0 hb0, map_div₀]
  have hden : 𝔭.valuation K (B * (b : K)) = exp (-((2 * k : ℕ) : ℤ)) := by
    rw [map_mul, hBv, hb', ← exp_add]; congr 1; push_cast; ring
  have hnum : 𝔭.valuation K (A * (b : K) - B * (a : K)) ≤ exp (-(N : ℤ)) := by
    rw [show A * (b : K) - B * (a : K) = A * ((b : K) - B) + B * (A - (a : K)) by ring]
    apply Valuation.map_add_le
    · rw [map_mul, ← Valuation.map_neg _ ((b : K) - B), neg_sub]
      calc 𝔭.valuation K A * 𝔭.valuation K (B - (b : K)) ≤ 1 * exp (-(N : ℤ)) :=
            mul_le_mul' hAle hB
        _ = exp (-(N : ℤ)) := one_mul _
    · rw [map_mul, hBv]
      calc exp (-(k : ℤ)) * 𝔭.valuation K (A - (a : K)) ≤ 1 * exp (-(N : ℤ)) :=
            mul_le_mul' (by rw [← exp_zero, exp_le_exp]; omega) hA
        _ = exp (-(N : ℤ)) := one_mul _
  rw [hden, div_le_one₀ (zero_lt_iff.mpr exp_ne_zero)]
  refine hnum.trans ?_
  rw [exp_le_exp]; push_cast; omega

/-- **(P5)** `K_𝔭 = ℚ + 𝓞_𝔭` when `N𝔭 = p` and `𝔭² ∤ p` (PROVED). -/
theorem exists_rat_sub_mem_integers (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hN : Ideal.absNorm 𝔭.asIdeal = p) (hu : UnramifiedOver 𝔭 p)
    (ι : ℚ →+* 𝔭.adicCompletion K) (x : 𝔭.adicCompletion K) :
    ∃ q : ℚ, x - ι q ∈ 𝔭.adicCompletionIntegers K := by
  obtain ⟨y, hy⟩ := exists_sub_mem_integers x
  obtain ⟨q, hq⟩ := exists_rat_sub_valuation_le_one hp h𝔭 hN hu y
  refine ⟨q, ?_⟩
  have h2 : algebraMap K (𝔭.adicCompletion K) y - ι q ∈ 𝔭.adicCompletionIntegers K := by
    rw [iota_eq, show ((q : K) : 𝔭.adicCompletion K) = algebraMap K (𝔭.adicCompletion K) (q : K)
      from rfl, ← map_sub, mem_adicCompletionIntegers,
      show algebraMap K (𝔭.adicCompletion K) (y - q) = ((y - q : K) : 𝔭.adicCompletion K) from rfl,
      valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := 𝔭)]
    exact hq
  have := add_mem hy h2
  rwa [sub_add_sub_cancel] at this

/-- **(P6)** At an unramified `𝔭 ∣ p`, every `x ≠ 0` of `K_𝔭` is `ι q` times a unit of `𝓞_𝔭`
(`q` a power of `p`) (PROVED). -/
theorem exists_rat_associated (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p)
    (hu : UnramifiedOver 𝔭 p) (ι : ℚ →+* 𝔭.adicCompletion K) {x : 𝔭.adicCompletion K}
    (hx : x ≠ 0) :
    ∃ q : ℚ, q ≠ 0 ∧ x / ι q ∈ 𝔭.adicCompletionIntegers K ∧
      ι q / x ∈ 𝔭.adicCompletionIntegers K := by
  have hvx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set m := log (Valued.v x)
  have hvx : Valued.v x = exp m := (exp_log hvx0).symm
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨(p : ℚ) ^ (-m), zpow_ne_zero _ hp0, ?_⟩
  have hvp : Valued.v (ι (p : ℚ)) = exp (-1 : ℤ) := by
    rw [valued_iota, valuation_ratCast]
    rw [show ((p : ℚ)).num = p from rfl, show ((p : ℚ)).den = 1 from rfl]
    rw [intValuation_prime_eq hp h𝔭 hu]
    simp
  have hvq : Valued.v (ι ((p : ℚ) ^ (-m))) = exp m := by
    rw [map_zpow₀, map_zpow₀, hvp, ← exp_zsmul]
    congr 1; simp
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, map_div₀, map_div₀, hvq, hvx,
    div_self exp_ne_zero]
  exact ⟨le_rfl, le_rfl⟩

/-! ### The place of `ℚ` -/

/-- **(P7)** `v` is a prime of `ℚ` above `natGenerator v` (PROVED). -/
theorem mem_primesAbove_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ primesAbove ℚ (Rat.HeightOneSpectrum.natGenerator v) := by
  have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff v
    (n := Rat.HeightOneSpectrum.natGenerator v)).mp dvd_rfl
  show (((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) : 𝓞 ℚ) ∈ v.asIdeal
  rw [Ideal.mem_map_of_equiv] at h
  obtain ⟨y, hy, hyp⟩ := h
  convert hy
  apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
  rw [hyp, map_intCast]
  push_cast; rfl

/-- **(P7)** `N v = natGenerator v` (PROVED). -/
theorem absNorm_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = Rat.HeightOneSpectrum.natGenerator v := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (Ideal.quotientEquiv v.asIdeal
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) v.asIdeal)
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) rfl).toEquiv,
    ← Rat.HeightOneSpectrum.span_natGenerator,
    Nat.card_congr (Int.quotientSpanEquivZMod _).toEquiv, Int.natAbs_natCast, Nat.card_zmod]

/-- **(P7)** `v² ∤ p` in `𝓞_ℚ` (PROVED). -/
theorem unramifiedOver_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    UnramifiedOver v (Rat.HeightOneSpectrum.natGenerator v) := by
  intro h
  -- `p 𝓞_ℚ = v`
  have hspan : Ideal.span {(((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) : 𝓞 ℚ)} =
      v.asIdeal := by
    set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
    have h1 := Rat.HeightOneSpectrum.span_natGenerator v
    ext x
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact Ideal.mul_mem_right _ _ (mem_primesAbove_rat v)
    · intro hx
      have hex : e x ∈ Ideal.map e v.asIdeal := Ideal.mem_map_of_mem _ hx
      rw [← h1, Ideal.mem_span_singleton] at hex
      obtain ⟨k, hk⟩ := hex
      refine ⟨e.symm k, ?_⟩
      apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, map_intCast, hk]
      push_cast; rfl
  rw [hspan] at h
  have hv0 : v.asIdeal ≠ 0 := by rw [Ne, Ideal.zero_eq_bot]; exact v.ne_bot
  have h1 : v.asIdeal * v.asIdeal ∣ v.asIdeal * 1 := by rw [mul_one, ← sq]; exact h
  have h2 := (mul_dvd_mul_iff_left hv0).mp h1
  have h3 := Ideal.le_of_dvd h2
  rw [Ideal.one_eq_top] at h3
  exact v.isPrime.ne_top (top_le_iff.mp h3)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
