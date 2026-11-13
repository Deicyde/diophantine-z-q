import Mathlib

/-! prop-ts-glue: development file for `SNLocalData` (imports Mathlib only; the result is pasted
into `PropTSGlue.lean`). -/

open Polynomial

noncomputable section

namespace PropTSGlueDev

abbrev zxMap (E : Type) [Field E] [Algebra ℚ[X] E] : ℤ[X] →+* E :=
  (algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem zxMap_injective (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] : Function.Injective (zxMap E) := by
  intro a b h
  simp only [zxMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E] at h
  have h1 := (algebraMap (RatFunc ℚ) E).injective h
  have h2 := (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) h1
  exact Polynomial.map_injective _ Int.cast_injective h2

@[reducible] noncomputable def locAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E]
    [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] (m : Ideal ℤ[X]) [m.IsPrime] :
    Algebra (Localization.AtPrime m) E :=
  (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) (g := zxMap E)
    (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      apply y.2
      rw [(zxMap_injective E) (h.trans (map_zero _).symm)]
      exact m.zero_mem)).toAlgebra

/-- `ℚ(X)` is the fraction field of `ℤ[X]` (through `ℤ[X] → ℚ[X] → ℚ(X)`). -/
theorem isFractionRing_zx :
    letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
    IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := zxMap_injective (RatFunc ℚ)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact nonZeroDivisors.coe_ne_zero y (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨⟨P, Q⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors ℚ[X]) z
    obtain ⟨bP, hbPM, hbP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
    obtain ⟨bQ, hbQM, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ)
      (Q : ℚ[X])
    set P' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
    set Q' := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q : ℚ[X])
    have hbP0 : bP ≠ 0 := nonZeroDivisors.ne_zero hbPM
    have hbQ0 : bQ ≠ 0 := nonZeroDivisors.ne_zero hbQM
    have hQ0 : (Q : ℚ[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero Q
    have hmapQ : Q'.map (Int.castRingHom ℚ) = C (bQ : ℚ) * Q := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbQ
    have hmapP : P'.map (Int.castRingHom ℚ) = C (bP : ℚ) * P := by
      rw [← smul_eq_C_mul]
      simpa [Algebra.smul_def] using hbP
    have hy : C bP * Q' ∈ nonZeroDivisors ℤ[X] := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      refine mul_ne_zero (by simpa using hbP0) ?_
      intro h0
      have := hmapQ
      rw [h0, Polynomial.map_zero] at this
      exact mul_ne_zero (by simpa using hbQ0) hQ0 this.symm
    refine ⟨⟨C bQ * P', ⟨_, hy⟩⟩, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, zxMap, RingHom.comp_apply, coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_C, hmapP, hmapQ, map_mul, eq_intCast]
    rw [← hz]
    simp only [map_intCast, Int.cast_id, Polynomial.map_intCast]
    ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

/-- **`SNLocalData` holds** (the normalization of `ℤ[X]_m` in `E` is normal, finite, and
contains `ℤ[X]_m`). -/
theorem snLocalData_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (m : Ideal ℤ[X]) [m.IsMaximal] :
    letI := locAlg E m
    IsIntegrallyClosed (integralClosure (Localization.AtPrime m) E) ∧
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) ∧
    Function.Injective
      (algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)) := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  letI iK : Algebra (Localization.AtPrime m) (RatFunc ℚ) := locAlg (RatFunc ℚ) m
  letI iZ : Algebra ℤ[X] (RatFunc ℚ) := (zxMap (RatFunc ℚ)).toAlgebra
  have hZ : IsFractionRing ℤ[X] (RatFunc ℚ) := isFractionRing_zx
  have hT1 : IsScalarTower ℤ[X] (Localization.AtPrime m) (RatFunc ℚ) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hfr : IsFractionRing (Localization.AtPrime m) (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl _ _
  have hT2 : IsScalarTower (Localization.AtPrime m) (RatFunc ℚ) E := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext m.primeCompl
    rw [RingHom.comp_assoc]
    change (IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime m)) =
      (algebraMap (RatFunc ℚ) E).comp
        ((IsLocalization.lift _).comp (algebraMap ℤ[X] (Localization.AtPrime m)))
    rw [IsLocalization.lift_comp, IsLocalization.lift_comp]
    simp only [zxMap, ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have hic : IsIntegrallyClosed (Localization.AtPrime m) :=
    isIntegrallyClosed_of_isLocalization _ m.primeCompl m.primeCompl_le_nonZeroDivisors
  refine ⟨integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc ℚ),
    IsIntegralClosure.finite (Localization.AtPrime m) (RatFunc ℚ) E
      (integralClosure (Localization.AtPrime m) E), ?_⟩
  intro a b h
  have h1 := congrArg Subtype.val h
  simp only [IntermediateField.algebraMap_apply, Subalgebra.coe_algebraMap] at h1
  rw [IsScalarTower.algebraMap_apply (Localization.AtPrime m) (RatFunc ℚ) E,
    IsScalarTower.algebraMap_apply (Localization.AtPrime m) (RatFunc ℚ) E] at h1
  exact IsFractionRing.injective (Localization.AtPrime m) (RatFunc ℚ)
    ((algebraMap (RatFunc ℚ) E).injective h1)

/-- `p`-integral rational has denominator prime to `p`. -/
theorem not_dvd_den_of_nonneg (p : ℕ) [hp : Fact p.Prime] (s : ℚ) (hs : 0 ≤ padicValRat p s) :
    ¬ p ∣ s.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ s.num := by
    intro hn
    have h1 : p ∣ s.num.natAbs := Int.natCast_dvd.mp hn
    exact hp.out.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h1 s.reduced).eq_one_of_dvd hd)
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum] at hs
  have := one_le_padicValNat_of_dvd s.den_nz hd
  omega

/-- **Clearing `p`-integral denominators**: a polynomial with `p`-integral coefficients times an
integer `N` prime to `p` has integer coefficients. -/
theorem exists_int_multiple (p : ℕ) [hp : Fact p.Prime] (f : ℚ[X])
    (hf : ∀ i, 0 ≤ padicValRat p (f.coeff i)) :
    ∃ N : ℤ, ¬ (p : ℤ) ∣ N ∧ ∃ F : ℤ[X], F.map (Int.castRingHom ℚ) = C (N : ℚ) * f := by
  refine ⟨∏ i ∈ f.support, ((f.coeff i).den : ℤ), ?_, ?_⟩
  · intro hdvd
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hpr _).mp hdvd
    exact not_dvd_den_of_nonneg p _ (hf i) (Int.natCast_dvd_natCast.mp hi)
  · rw [← mem_lifts, lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    by_cases hn : n ∈ f.support
    · obtain ⟨M', hM'⟩ := Finset.dvd_prod_of_mem (fun i => ((f.coeff i).den : ℤ)) hn
      refine ⟨M' * (f.coeff n).num, ?_⟩
      simp only [eq_intCast, Int.cast_mul]
      rw [hM', Int.cast_mul, ← Rat.den_mul_eq_num]
      push_cast
      ring
    · rw [notMem_support_iff.mp hn, mul_zero]
      exact ⟨0, by simp⟩

/-- `C n ∉ m` when `C p ∈ m` and `p ∤ n` (`m` proper). -/
theorem C_notMem (p : ℕ) [hp : Fact p.Prime] (m : Ideal ℤ[X]) (hm : m ≠ ⊤)
    (hpm : C (p : ℤ) ∈ m) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : C n ∉ m := by
  intro hnm
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨α, β, h⟩ := (Prime.coprime_iff_not_dvd hpr).mpr hn
  apply hm
  rw [Ideal.eq_top_iff_one]
  have : C (α * p + β * n) ∈ m := by
    rw [map_add, map_mul, map_mul]
    exact m.add_mem (m.mul_mem_left _ hpm) (m.mul_mem_left _ hnm)
  rwa [h, map_one] at this

/-- **Reduction mod `(p, dX − a)`**: `d^k F ≡ Σ c_i a^i d^{k−i}` modulo any ideal containing
`dX − a` (`k = deg F`). -/
theorem homog_mem (m : Ideal ℤ[X]) (a d : ℤ) (hm : C d * X - C a ∈ m) (F : ℤ[X]) :
    C (d ^ F.natDegree) * F -
      C (∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * a ^ i * d ^ (F.natDegree - i)) ∈ m := by
  set k := F.natDegree
  have hF : F = ∑ i ∈ Finset.range (k + 1), C (F.coeff i) * X ^ i := as_sum_range_C_mul_X_pow F
  nth_rw 1 [hF]
  rw [Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Ideal.sum_mem
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e : C (d ^ k) * (C (F.coeff i) * X ^ i) - C (F.coeff i * a ^ i * d ^ (k - i)) =
      C (F.coeff i * d ^ (k - i)) * ((C d * X) ^ i - C a ^ i) := by
    rw [show d ^ k = d ^ (k - i) * d ^ i by rw [← pow_add, Nat.sub_add_cancel hik]]
    simp only [map_mul, map_pow]
    ring
  rw [e]
  apply m.mul_mem_left
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (C d * X) (C a) i
  rw [hq]
  exact m.mul_mem_right _ hm

/-- **A polynomial `F ∈ ℤ[X]` with `F(s₀)` a `p`-adic unit is not in `m`**, for any proper
ideal `m` containing `p` and `dX − a` (`s₀ = a/d`). -/
theorem notMem_of_val_zero (p : ℕ) [hp : Fact p.Prime] (s₀ : ℚ) (hs₀ : 0 ≤ padicValRat p s₀)
    (m : Ideal ℤ[X]) (hm : m ≠ ⊤) (hpm : C (p : ℤ) ∈ m)
    (hsm : C (s₀.den : ℤ) * X - C s₀.num ∈ m) (F : ℤ[X])
    (hne : (F.map (Int.castRingHom ℚ)).eval s₀ ≠ 0)
    (hval : padicValRat p ((F.map (Int.castRingHom ℚ)).eval s₀) = 0) : F ∉ m := by
  intro hF
  set k := F.natDegree
  set d : ℤ := (s₀.den : ℤ) with hd
  set n₀ : ℤ := ∑ i ∈ Finset.range (k + 1), F.coeff i * s₀.num ^ i * d ^ (k - i)
  have hd0 : (d : ℚ) ≠ 0 := by simp [d]
  have hrel : (n₀ : ℚ) = (d : ℚ) ^ k * (F.map (Int.castRingHom ℚ)).eval s₀ := by
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective (RingHom.injective_int _), Finset.mul_sum]
    simp only [n₀, Int.cast_sum, Int.cast_mul, Int.cast_pow, coeff_map, eq_intCast]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hs : (s₀.num : ℚ) = (d : ℚ) * s₀ := by simp [d]
    rw [hs, show (d : ℚ) ^ k = (d : ℚ) ^ (k - i) * (d : ℚ) ^ i by
      rw [← pow_add, Nat.sub_add_cancel hik]]
    ring
  have hn₀ : ¬ (p : ℤ) ∣ n₀ := by
    intro hdvd
    have hn0 : (n₀ : ℚ) ≠ 0 := by rw [hrel]; exact mul_ne_zero (pow_ne_zero _ hd0) hne
    have hdv : padicValRat p (d : ℚ) = 0 := by
      rw [show (d : ℚ) = ((s₀.den : ℕ) : ℚ) by simp [d], ← padicValRat_of_nat,
        padicValNat.eq_zero_of_not_dvd (not_dvd_den_of_nonneg p s₀ hs₀)]
      rfl
    have hv : padicValRat p (n₀ : ℚ) = 0 := by
      rw [hrel, padicValRat.mul (pow_ne_zero _ hd0) hne, padicValRat.pow, hdv, hval]
      simp
    rw [padicValRat.of_int] at hv
    have hn0' : n₀ ≠ 0 := by exact_mod_cast hn0
    have := padicValInt_dvd_iff (p := p) 1 n₀
    simp only [pow_one] at this
    have hv' : padicValInt p n₀ = 0 := by exact_mod_cast hv
    rw [hv'] at this
    have h2 := this.mp hdvd
    rcases h2 with h2 | h2
    · exact hn0' h2
    · omega
  apply C_notMem p m hm hpm n₀ hn₀
  have h1 : C (d ^ k) * F - C n₀ ∈ m := homog_mem m s₀.num d hsm F
  have h2 : C (d ^ k) * F ∈ m := m.mul_mem_left _ hF
  have := m.sub_mem h2 h1
  rwa [sub_sub_cancel] at this

end PropTSGlueDev

#print axioms PropTSGlueDev.isFractionRing_zx
#print axioms PropTSGlueDev.snLocalData_aux
