import Mathlib

/-! prop-ts-glue: development file for `SNSpecializeUnram` (Mathlib only). -/

open Polynomial

noncomputable section

namespace PropTSGlueDev4

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

theorem isLocalization_field_self {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (M : Submonoid A) (hM : ∀ x ∈ M, algebraMap A K x ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by simpa using hM x hx)
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

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

open NumberField in
def UnramifiedAt (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P →
    P.ramificationIdx ℤ = 1

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


/-- `n(u) = Σ u_i a^i d^{k−i}` (so that `n(u) = d^k u(s₀)`). -/
def nval (s₀ : ℚ) (u : ℤ[X]) : ℤ :=
  ∑ i ∈ Finset.range (u.natDegree + 1), u.coeff i * s₀.num ^ i * (s₀.den : ℤ) ^ (u.natDegree - i)

theorem nval_cast (s₀ : ℚ) (u : ℤ[X]) :
    (nval s₀ u : ℚ) = (s₀.den : ℚ) ^ u.natDegree * (u.map (Int.castRingHom ℚ)).eval s₀ := by
  set k := u.natDegree
  rw [eval_eq_sum_range, natDegree_map_eq_of_injective (RingHom.injective_int _), Finset.mul_sum]
  simp only [nval, Int.cast_sum, Int.cast_mul, Int.cast_pow, coeff_map, eq_intCast, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hs : (s₀.num : ℚ) = (s₀.den : ℚ) * s₀ := by simp
  rw [hs, show (s₀.den : ℚ) ^ k = (s₀.den : ℚ) ^ (k - i) * (s₀.den : ℚ) ^ i by
    rw [← pow_add, Nat.sub_add_cancel hik]]
  ring

/-- **Membership in `m = (p, dX − a)`**: `u ∈ m ↔ p ∣ n(u)`. -/
theorem mem_m_iff (p : ℕ) [hp : Fact p.Prime] (s₀ : ℚ) (hs₀ : 0 ≤ padicValRat p s₀)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hsm : C (s₀.den : ℤ) * X - C s₀.num ∈ m) (u : ℤ[X]) :
    u ∈ m ↔ (p : ℤ) ∣ nval s₀ u := by
  have hm : m ≠ ⊤ := Ideal.IsMaximal.ne_top ‹_›
  have h1 : C ((s₀.den : ℤ) ^ u.natDegree) * u - C (nval s₀ u) ∈ m := homog_mem m s₀.num _ hsm u
  have hd : ¬ (p : ℤ) ∣ (s₀.den : ℤ) ^ u.natDegree := by
    intro h
    exact not_dvd_den_of_nonneg p s₀ hs₀
      (Int.natCast_dvd_natCast.mp ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h))
  constructor
  · intro hu
    by_contra hn
    apply C_notMem p m hm hpm _ hn
    have := m.sub_mem (m.mul_mem_left (C ((s₀.den : ℤ) ^ u.natDegree)) hu) h1
    rwa [sub_sub_cancel] at this
  · intro hn
    obtain ⟨c, hc⟩ := hn
    have hCn : C (nval s₀ u) ∈ m := by rw [hc, C_mul]; exact m.mul_mem_right _ hpm
    have h2 : C ((s₀.den : ℤ) ^ u.natDegree) * u ∈ m := by
      have := m.add_mem h1 hCn
      rwa [sub_add_cancel] at this
    have hmp : m.IsPrime := Ideal.IsMaximal.isPrime ‹_›
    rcases hmp.mem_or_mem h2 with h | h
    · exact absurd h (C_notMem p m hm hpm _ hd)
    · exact h

/-- The generator `dX − a` of the section `X = s₀`. -/
def secGen (s₀ : ℚ) : ℤ[X] := C (s₀.den : ℤ) * X - C s₀.num

/-- Evaluation at `s₀` on `ℤ[X]_m` (denominators do not vanish at `s₀`). -/
def evR (p : ℕ) [Fact p.Prime] (s₀ : ℚ) (hs₀ : 0 ≤ padicValRat p s₀)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hsm : C (s₀.den : ℤ) * X - C s₀.num ∈ m) : Localization.AtPrime m →+* ℚ :=
  IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m)
    (g := Polynomial.eval₂RingHom (Int.castRingHom ℚ) s₀) (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h0
      apply y.2
      show (y : ℤ[X]) ∈ m
      rw [mem_m_iff p s₀ hs₀ m hpm hsm]
      have h1 := nval_cast s₀ y.1
      have h2 : ((y.1).map (Int.castRingHom ℚ)).eval s₀ = 0 := by
        rw [eval_map]; exact h0
      rw [h2, mul_zero] at h1
      have : nval s₀ y.1 = 0 := by exact_mod_cast h1
      rw [this]
      exact dvd_zero _)

theorem rbar_isLocalization (p : ℕ) [hp : Fact p.Prime] (s₀ : ℚ) (hs₀ : 0 ≤ padicValRat p s₀)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hsm : C (s₀.den : ℤ) * X - C s₀.num ∈ m) :
    IsLocalization (Ideal.span {(p : ℤ)}).primeCompl
      (Localization.AtPrime m ⧸ Ideal.span {algebraMap ℤ[X] (Localization.AtPrime m) (secGen s₀)}) := by
  set R := Localization.AtPrime m
  set g : R := algebraMap ℤ[X] R (secGen s₀) with hg
  set I : Ideal R := Ideal.span {g} with hI
  set ev := evR p s₀ hs₀ m hpm hsm
  have hev : ∀ F : ℤ[X], ev (algebraMap ℤ[X] R F) = F.eval₂ (Int.castRingHom ℚ) s₀ :=
    fun F => IsLocalization.lift_eq _ F
  have hevI : I ≤ RingHom.ker ev := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hg, hev,
      secGen]
    rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
    simp only [eq_intCast, Int.cast_natCast]
    rw [Rat.den_mul_eq_num, sub_self]
  set evb : R ⧸ I →+* ℚ := Ideal.Quotient.lift I ev hevI
  have hevb : ∀ n : ℤ, evb (algebraMap ℤ (R ⧸ I) n) = n := fun n => by simp
  -- the ideal `I` pulled back to `ℤ[X]` contains `dX − a`
  set J : Ideal ℤ[X] := (I.comap (algebraMap ℤ[X] R)) with hJ
  have hJ : C (s₀.den : ℤ) * X - C s₀.num ∈ J := Ideal.subset_span rfl
  have hmkF : ∀ F : ℤ[X], algebraMap ℤ (R ⧸ I) ((s₀.den : ℤ) ^ F.natDegree) *
      Ideal.Quotient.mk I (algebraMap ℤ[X] R F) = algebraMap ℤ (R ⧸ I) (nval s₀ F) := by
    intro F
    have h := homog_mem J s₀.num _ hJ F
    have h' : Ideal.Quotient.mk I (algebraMap ℤ[X] R (C ((s₀.den : ℤ) ^ F.natDegree) * F -
        C (nval s₀ F))) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    simp only [map_sub, map_mul] at h'
    rw [sub_eq_zero] at h'
    have e1 : ∀ n : ℤ, Ideal.Quotient.mk I (algebraMap ℤ[X] R (C n)) = algebraMap ℤ (R ⧸ I) n :=
      fun n => by simp
    rw [e1, e1] at h'
    exact h'
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy' : ¬ (p : ℤ) ∣ y := fun h => hy (Ideal.mem_span_singleton.mpr h)
    have hCy : C y ∉ m := C_notMem p m (Ideal.IsMaximal.ne_top ‹_›) hpm y hy'
    have hu : IsUnit (algebraMap ℤ[X] R (C y)) :=
      IsLocalization.map_units R (⟨C y, hCy⟩ : m.primeCompl)
    have := hu.map (Ideal.Quotient.mk I)
    simpa using this
  · intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨F, u, hu⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl r
    have hnu : ¬ (p : ℤ) ∣ nval s₀ u := fun h => hu ((mem_m_iff p s₀ hs₀ m hpm hsm u).mpr h)
    have hd : ¬ (p : ℤ) ∣ (s₀.den : ℤ) ^ F.natDegree := by
      intro h
      exact not_dvd_den_of_nonneg p s₀ hs₀
        (Int.natCast_dvd_natCast.mp ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h))
    have hmem : nval s₀ u * (s₀.den : ℤ) ^ F.natDegree ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
      intro h
      rcases (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp.out) |>.mem_or_mem h with h | h
      · exact hnu (Ideal.mem_span_singleton.mp h)
      · exact hd (Ideal.mem_span_singleton.mp h)
    refine ⟨⟨nval s₀ F * (s₀.den : ℤ) ^ u.natDegree, ⟨_, hmem⟩⟩, ?_⟩
    have hspec : IsLocalization.mk' R F (⟨u, hu⟩ : m.primeCompl) * algebraMap ℤ[X] R u =
        algebraMap ℤ[X] R F := IsLocalization.mk'_spec R F ⟨u, hu⟩
    have h1 := hmkF F
    have h2 := hmkF u
    simp only [map_mul]
    rw [← h1, ← h2, ← hspec, map_mul]
    ring
  · intro x y h
    have := congrArg evb h
    rw [hevb, hevb] at this
    have hxy : x = y := by exact_mod_cast this
    exact ⟨1, by rw [hxy]⟩

/-- An integrally closed subring `A` of a field `K` contains every element of its subfield closure
that is integral over `ℤ`. -/
theorem mem_of_isIntegral_of_mem_closure {K : Type*} [Field K] (A : Subring K)
    [IsIntegrallyClosed A] {x : K} (hx : x ∈ Subfield.closure (A : Set K)) (hint : IsIntegral ℤ x) :
    x ∈ A := by
  rw [Subfield.mem_closure_iff] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  rw [Subring.closure_eq] at ha hb
  by_cases hb0 : b = 0
  · rw [hb0, div_zero] at hab
    rw [← hab]
    exact A.zero_mem
  have hbA : (⟨b, hb⟩ : A) ∈ nonZeroDivisors A :=
    mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))
  let ι : FractionRing A →+* K := IsFractionRing.lift A.subtype_injective
  let z : FractionRing A := IsLocalization.mk' (FractionRing A) (⟨a, ha⟩ : A) ⟨⟨b, hb⟩, hbA⟩
  have hz : ι z = x := by
    show IsFractionRing.lift A.subtype_injective (IsLocalization.mk' (FractionRing A)
      (⟨a, ha⟩ : A) ⟨⟨b, hb⟩, hbA⟩) = x
    rw [IsFractionRing.lift_mk']
    exact hab
  have hzint : IsIntegral ℤ z := by
    obtain ⟨f, hfm, hf⟩ := hint
    refine ⟨f, hfm, ι.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hz]
    have hsub : ι.comp (algebraMap ℤ (FractionRing A)) = algebraMap ℤ K := Subsingleton.elim _ _
    rw [hsub]
    exact hf
  have hzintA : IsIntegral A z := hzint.tower_top
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzintA
  rw [← hz, ← hc]
  show IsFractionRing.lift A.subtype_injective (algebraMap A (FractionRing A) c) ∈ A
  rw [IsFractionRing.lift_algebraMap]
  exact c.2

abbrev Qbar : Type := AlgebraicClosure ℚ

/-- **The finiteness half of `SNSpecialize` is a theorem**: the residue field of `B` at a prime
over `X − s₀`, embedded in `ℚ̄`, generates a number field (`B` is a finite `ℚ[X]`-module, and
`ℚ[X]` acts on `B/𝔓` through `X ↦ s₀`). -/
theorem finiteDimensional_residue (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (s₀ : ℚ)
    (𝔓 : Ideal (integralClosure ℚ[X] E)) (hU : 𝔓.under ℚ[X] = Ideal.span {X - C s₀})
    (φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* Qbar) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range φ)) := by
  have hfin : Module.Finite ℚ[X] (integralClosure ℚ[X] E) :=
    IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  obtain ⟨s, hs⟩ := hfin.fg_top
  set T : Set Qbar := (fun b => φ (Ideal.Quotient.mk 𝔓 b)) '' (s : Set _) with hTdef
  have hTfin : Finite T := Set.Finite.to_subtype (s.finite_toSet.image _)
  have key : ∀ f : ℚ[X], φ (Ideal.Quotient.mk 𝔓 (algebraMap ℚ[X] (integralClosure ℚ[X] E) f)) =
      algebraMap ℚ Qbar (f.eval s₀) := by
    intro f
    have hmem : f - C (f.eval s₀) ∈ 𝔓.under ℚ[X] := by
      rw [hU, Ideal.mem_span_singleton]
      exact X_sub_C_dvd_sub_C_eval
    have h1 : Ideal.Quotient.mk 𝔓 (algebraMap ℚ[X] (integralClosure ℚ[X] E) f) =
        Ideal.Quotient.mk 𝔓 (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (f.eval s₀))) := by
      rw [Ideal.Quotient.eq, ← map_sub]
      exact hmem
    rw [h1]
    have hsub : ((φ.comp (Ideal.Quotient.mk 𝔓)).comp
        ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp C) : ℚ →+* Qbar) = algebraMap ℚ Qbar :=
      Subsingleton.elim _ _
    exact congrArg (fun g : ℚ →+* Qbar => g (f.eval s₀)) hsub
  have hle : IntermediateField.adjoin ℚ (Set.range φ) ≤ IntermediateField.adjoin ℚ T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hb : b ∈ Submodule.span ℚ[X] (s : Set (integralClosure ℚ[X] E)) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add, RingHom.map_add]; exact add_mem hy hz
    | smul f y _ hy =>
      rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, key]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  have hT : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

theorem atPrime_congr {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (h : p = q) [IsLocalization.AtPrime S p] :
    IsLocalization.AtPrime S q := by
  subst h
  assumption

/-- Integrality over `ℤ` descends along an injective ring hom. -/
theorem isIntegral_int_of_injective {K₁ K₂ : Type*} [CommRing K₁] [CommRing K₂] (f : K₁ →+* K₂)
    (hf : Function.Injective f) {x : K₁} (h : IsIntegral ℤ (f x)) : IsIntegral ℤ x := by
  obtain ⟨q, hqm, hq⟩ := h
  refine ⟨q, hqm, hf ?_⟩
  rw [Polynomial.hom_eval₂, map_zero]
  have hsub : f.comp (algebraMap ℤ K₁) = algebraMap ℤ K₂ := Subsingleton.elim _ _
  rw [hsub]
  exact hq

/-- Integrality over `ℤ` is preserved by ring homs. -/
theorem isIntegral_int_map {K₁ K₂ : Type*} [CommRing K₁] [CommRing K₂] (f : K₁ →+* K₂)
    {x : K₁} (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) := by
  obtain ⟨q, hqm, hq⟩ := h
  refine ⟨q, hqm, ?_⟩
  have hsub : algebraMap ℤ K₂ = f.comp (algebraMap ℤ K₁) := Subsingleton.elim _ _
  rw [hsub, ← Polynomial.hom_eval₂, hq, map_zero]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
attribute [local instance] Polynomial.algebra in
theorem snSpecializeUnram_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (s₀ : ℚ) (hs₀ : 0 ≤ padicValRat p s₀) (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m)
    (hsm : C (s₀.den : ℤ) * X - C s₀.num ∈ m) :
    letI := locAlg E m
    Algebra.Etale (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) →
    ∀ 𝔓 : Ideal (integralClosure ℚ[X] E), 𝔓.IsPrime →
      𝔓.under ℚ[X] = Ideal.span {X - C s₀} →
      ∀ φ : integralClosure ℚ[X] E ⧸ 𝔓 →+* AlgebraicClosure ℚ,
        UnramifiedAt (IntermediateField.adjoin ℚ (Set.range φ)) p := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  letI cS : CommRing (integralClosure (Localization.AtPrime m) E) := inferInstance
  letI cS' : CommSemiring (integralClosure (Localization.AtPrime m) E) := CommRing.toCommSemiring
  letI cS'' : Semiring (integralClosure (Localization.AtPrime m) E) := CommSemiring.toSemiring
  intro het 𝔓 h𝔓 hU φ
  have : Fact p.Prime := ⟨hp⟩
  -- the rings
  letI iZ : Algebra ℤ[X] E := (zxMap E).toAlgebra
  have hTR : IsScalarTower ℤ[X] (Localization.AtPrime m) E := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hTQ : IsScalarTower ℤ[X] ℚ[X] E := IsScalarTower.of_algebraMap_eq' rfl
  let ιS : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime m) E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime m) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCS := ιS.toAlgebra
  have hCSE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
      E := IsScalarTower.of_algebraMap_eq' rfl
  have hZCS : IsScalarTower ℤ[X] (integralClosure ℤ[X] E)
      (integralClosure (Localization.AtPrime m) E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E)]
    change algebraMap (Localization.AtPrime m) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
    exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
  have hlocE : IsLocalization (Algebra.algebraMapSubmonoid E m.primeCompl) E :=
    isLocalization_field_self _ (fun x hx h0 => hx (by
      rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact m.zero_mem))
  have hlocS : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E)
      m.primeCompl) (integralClosure (Localization.AtPrime m) E) :=
    IsLocalization.integralClosure m.primeCompl
  let ιB : integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := ℚ[X]) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCB := ιB.toAlgebra
  have hCBE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hZCB : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] ℚ[X] (integralClosure ℚ[X] E)]
    rfl
  -- the map `g : C → ℚ̄` and its values on `ℤ[X]`
  let g : integralClosure ℤ[X] E →+* AlgebraicClosure ℚ :=
    φ.comp ((Ideal.Quotient.mk 𝔓).comp (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)))
  have hkeyQ : ∀ f : ℚ[X], φ (Ideal.Quotient.mk 𝔓 (algebraMap ℚ[X] (integralClosure ℚ[X] E) f)) =
      algebraMap ℚ (AlgebraicClosure ℚ) (f.eval s₀) := by
    intro f
    have hmem : f - C (f.eval s₀) ∈ 𝔓.under ℚ[X] := by
      rw [hU, Ideal.mem_span_singleton]
      exact X_sub_C_dvd_sub_C_eval
    have h1 : Ideal.Quotient.mk 𝔓 (algebraMap ℚ[X] (integralClosure ℚ[X] E) f) =
        Ideal.Quotient.mk 𝔓 (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C (f.eval s₀))) := by
      rw [Ideal.Quotient.eq, ← map_sub]
      exact hmem
    rw [h1]
    have hsub : ((φ.comp (Ideal.Quotient.mk 𝔓)).comp
        ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp C) : ℚ →+* AlgebraicClosure ℚ) =
        algebraMap ℚ (AlgebraicClosure ℚ) := Subsingleton.elim _ _
    exact congrArg (fun g : ℚ →+* AlgebraicClosure ℚ => g (f.eval s₀)) hsub
  have hkey : ∀ u : ℤ[X], g (algebraMap ℤ[X] (integralClosure ℤ[X] E) u) =
      algebraMap ℚ (AlgebraicClosure ℚ) ((u.map (Int.castRingHom ℚ)).eval s₀) := by
    intro u
    show φ (Ideal.Quotient.mk 𝔓 (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
      (algebraMap ℤ[X] (integralClosure ℤ[X] E) u))) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X] ℚ[X]
      (integralClosure ℚ[X] E)]
    exact hkeyQ _
  have hgu : ∀ y : Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl,
      IsUnit (g y) := by
    rintro ⟨_, u, hu, rfl⟩
    rw [hkey, isUnit_iff_ne_zero]
    intro h0
    have h0' : (u.map (Int.castRingHom ℚ)).eval s₀ = 0 :=
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective (h0.trans (map_zero _).symm)
    apply hu
    show u ∈ m
    rw [mem_m_iff p s₀ hs₀ m hpm hsm]
    have h1 := nval_cast s₀ u
    rw [h0', mul_zero] at h1
    have : nval s₀ u = 0 := by exact_mod_cast h1
    rw [this]
    exact dvd_zero _
  let Ψ : integralClosure (Localization.AtPrime m) E →+* AlgebraicClosure ℚ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl)
      hgu
  -- the image `A = Ψ(S) ⊆ ℚ̄` (the closed-fibre quotient) and its formal unramifiedness over `ℤ`
  set A : Subring (AlgebraicClosure ℚ) := Ψ.range with hA
  letI aRA0 : Algebra (Localization.AtPrime m) A :=
    (Ψ.rangeRestrict.comp (algebraMap (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E))).toAlgebra
  letI aSA : Algebra (integralClosure (Localization.AtPrime m) E) A := Ψ.rangeRestrict.toAlgebra
  have hTSA : IsScalarTower (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) A :=
    IsScalarTower.of_algebraMap_eq' rfl
  set I : Ideal (Localization.AtPrime m) :=
    Ideal.span {algebraMap ℤ[X] (Localization.AtPrime m) (secGen s₀)} with hI
  have hΨsec : Ψ (algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)
      (algebraMap ℤ[X] (Localization.AtPrime m) (secGen s₀))) = 0 := by
    rw [← IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime m),
      IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
        (integralClosure (Localization.AtPrime m) E)]
    rw [IsLocalization.lift_eq, hkey]
    rw [secGen, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, map_X,
      eval_sub, eval_mul, eval_C, eval_C, eval_X]
    simp only [eq_intCast, Int.cast_natCast]
    rw [Rat.den_mul_eq_num, sub_self, map_zero]
  have hIker : I ≤ RingHom.ker (algebraMap (Localization.AtPrime m) A) := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    apply Subtype.ext
    exact hΨsec
  letI aRbA : Algebra (Localization.AtPrime m ⧸ I) A :=
    (Ideal.Quotient.lift I (algebraMap (Localization.AtPrime m) A) hIker).toAlgebra
  have hTRA : IsScalarTower (Localization.AtPrime m) (Localization.AtPrime m ⧸ I) A :=
    IsScalarTower.of_algebraMap_eq (R := Localization.AtPrime m) (S := Localization.AtPrime m ⧸ I)
      (A := A) (fun x => rfl)
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E) A) := Ψ.rangeRestrict_surjective
  have hFU0 : Algebra.FormallyUnramified (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E) := inferInstance
  have hFU1 : Algebra.FormallyUnramified (Localization.AtPrime m) A :=
    Algebra.FormallyUnramified.of_surjective _ hsurj
  have hFU2 : Algebra.FormallyUnramified (Localization.AtPrime m ⧸ I) A :=
    Algebra.FormallyUnramified.of_restrictScalars (Localization.AtPrime m) _ _
  have hloc := rbar_isLocalization p s₀ hs₀ m hpm hsm
  have hFU3 : Algebra.FormallyUnramified ℤ (Localization.AtPrime m ⧸ I) :=
    Algebra.FormallyUnramified.of_isLocalization (Ideal.span {(p : ℤ)}).primeCompl
  haveI hTZ := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := Localization.AtPrime m ⧸ I) (A := A)
      (fun x => by simp only [eq_intCast, map_intCast])
  have hFU4 : Algebra.FormallyUnramified ℤ A :=
    Algebra.FormallyUnramified.comp ℤ (Localization.AtPrime m ⧸ I) A
  -- `R ⧸ I` (≅ `ℤ_(p)`) is a Dedekind domain, so `A` is a Dedekind domain
  have hRbdom : IsDomain (Localization.AtPrime m ⧸ I) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime m ⧸ I)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(p : ℤ)}))
  have hRbded : IsDedekindDomain (Localization.AtPrime m ⧸ I) :=
    IsLocalization.isDedekindDomain ℤ
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(p : ℤ)})) _
  have hfinS : Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E) :=
    (snLocalData_aux E m).2.1
  have hfinA : Module.Finite (Localization.AtPrime m) A :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E) A).toLinearMap hsurj
  letI mRbA : Module (Localization.AtPrime m ⧸ I) A := aRbA.toModule
  have hfinA' : Module.Finite (Localization.AtPrime m ⧸ I) A :=
    Module.Finite.of_restrictScalars_finite (Localization.AtPrime m) _ _
  have hAded : IsDedekindDomain A := IsDedekindDomain.of_formallyUnramified
    (Localization.AtPrime m ⧸ I) A
  -- `A ⊆ L`, and `L` lies in the fraction field of `A`
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ (Set.range φ)
    with hL
  have hgL : ∀ c : integralClosure ℤ[X] E, g c ∈ L := fun c =>
    IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
  have hgM : ∀ y : Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl,
      g y ≠ 0 := fun y => (hgu y).ne_zero
  have hΨmk : ∀ (c : integralClosure ℤ[X] E)
      (y : Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl),
      Ψ (IsLocalization.mk' (integralClosure (Localization.AtPrime m) E) c y) = g c / g y := by
    intro c y
    rw [IsLocalization.lift_mk'_spec, mul_div_cancel₀ _ (hgM y)]
  have hAL : ∀ a ∈ A, a ∈ L := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨⟨c, y⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl) s
    rw [hΨmk]
    exact div_mem (hgL c) (hgL y)
  have hgA : ∀ c : integralClosure ℤ[X] E, g c ∈ A := fun c =>
    ⟨algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E) c,
      IsLocalization.lift_eq _ c⟩
  -- `B` is a localization of `C`, so `L` lies in the fraction field of `A`
  let ιB : integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := ℚ[X]) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hgdef : ∀ c, g c = φ (Ideal.Quotient.mk 𝔓
      (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) c)) := fun c => rfl
  set M₀ : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map C with hM₀
  have hlocQ : IsLocalization M₀ ℚ[X] := Polynomial.isLocalization _ _
  have hlocE₀ : IsLocalization (Algebra.algebraMapSubmonoid E M₀) E :=
    isLocalization_field_self _ (by
      rintro _ ⟨n, hn, rfl⟩ h0
      have : C n = 0 := (zxMap_injective E) (h0.trans (map_zero _).symm)
      exact nonZeroDivisors.ne_zero hn (C_eq_zero.mp this))
  have hlocB : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀)
      (integralClosure ℚ[X] E) :=
    IsLocalization.integralClosure M₀
  have hrange : Set.range φ ⊆ Subfield.closure (A : Set (AlgebraicClosure ℚ)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨c, n⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀) b
    have hspec := IsLocalization.mk'_spec (integralClosure ℚ[X] E) c n
    have h1 : φ (Ideal.Quotient.mk 𝔓 (IsLocalization.mk' (integralClosure ℚ[X] E) c n)) * g n =
        g c := by
      rw [hgdef, hgdef, ← RingHom.map_mul, ← RingHom.map_mul, hspec]
    have hn0 : g n ≠ 0 := by
      obtain ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩⟩ := n
      show g (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C k)) ≠ 0
      rw [hkey, Polynomial.map_C, eval_C]
      simp only [eq_intCast, map_intCast, ne_eq, Int.cast_eq_zero]
      exact nonZeroDivisors.ne_zero hk
    rw [eq_div_of_mul_eq hn0 h1]
    exact div_mem (Subfield.subset_closure (hgA c)) (Subfield.subset_closure (hgA n))
  have hQsub : Set.range (algebraMap ℚ (AlgebraicClosure ℚ)) ⊆
      Subfield.closure (A : Set (AlgebraicClosure ℚ)) := by
    rintro _ ⟨q, rfl⟩
    rw [show algebraMap ℚ (AlgebraicClosure ℚ) q = (q.num : AlgebraicClosure ℚ) / (q.den : AlgebraicClosure ℚ) by
      rw [eq_div_iff (by exact_mod_cast q.den_nz)]
      simp only [eq_ratCast]
      exact_mod_cast Rat.mul_den_eq_num q]
    exact div_mem (Subfield.subset_closure (intCast_mem A q.num))
      (Subfield.subset_closure (natCast_mem A q.den))
  have hLsub : L.toSubfield ≤ Subfield.closure (A : Set (AlgebraicClosure ℚ)) :=
    IntermediateField.adjoin_le_subfield (F := ℚ) (S := Set.range φ)
      (K := Subfield.closure (A : Set (AlgebraicClosure ℚ))) hQsub hrange
  -- `𝓞 L ⊆ A` (`A` is integrally closed)
  have hOA : ∀ x : NumberField.RingOfIntegers L, ((x : L) : AlgebraicClosure ℚ) ∈ A := fun x =>
    mem_of_isIntegral_of_mem_closure A (hLsub (x : L).2)
      (isIntegral_int_map L.val.toRingHom x.2)
  -- `j : 𝓞 L → A`, and `A` is the localization of `𝓞 L` away from `p`
  let j : NumberField.RingOfIntegers L →+* A :=
    { toFun := fun x => ⟨((x : L) : AlgebraicClosure ℚ), hOA x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hj_inj : Function.Injective j := by
    intro x y h
    have h1 : ((x : L) : AlgebraicClosure ℚ) = ((y : L) : AlgebraicClosure ℚ) :=
      congrArg (fun z : A => (z : AlgebraicClosure ℚ)) h
    exact NumberField.RingOfIntegers.ext (Subtype.ext h1)
  letI aOA : Algebra (NumberField.RingOfIntegers L) A := j.toAlgebra
  set Mp : Submonoid ℤ := (Ideal.span {(p : ℤ)}).primeCompl with hMp
  have hunitA : ∀ n ∈ Mp, IsUnit (n : A) := by
    intro n hn
    have h0 : IsUnit (algebraMap ℤ (Localization.AtPrime m ⧸ I) n) :=
      IsLocalization.map_units (Localization.AtPrime m ⧸ I) (⟨n, hn⟩ : Mp)
    have h1 := RingHom.isUnit_map (Ideal.Quotient.lift I (algebraMap (Localization.AtPrime m) A)
      hIker) h0
    simpa using h1
  have hjint : ∀ n : ℤ, j (algebraMap ℤ (NumberField.RingOfIntegers L) n) = (n : A) := by
    intro n
    simp
  have hlocA : IsLocalization (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers L) Mp) A := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, hn, rfl⟩
      change IsUnit (j (algebraMap ℤ (NumberField.RingOfIntegers L) n))
      rw [hjint]
      exact hunitA n hn
    · intro a
      have hai : IsIntegral (Localization.AtPrime m ⧸ I) a := Algebra.IsIntegral.isIntegral a
      obtain ⟨⟨n, hn⟩, hnint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (R := ℤ) (M := Mp) (Rₘ := Localization.AtPrime m ⧸ I) a hai
      have hyL : ((n • a : A) : AlgebraicClosure ℚ) ∈ L := hAL _ (n • a).2
      have hyint : IsIntegral ℤ (⟨_, hyL⟩ : L) :=
        isIntegral_int_of_injective L.val.toRingHom L.val.injective
          (isIntegral_int_map A.subtype hnint)
      let y : NumberField.RingOfIntegers L := ⟨⟨_, hyL⟩, hyint⟩
      refine ⟨⟨y, ⟨_, n, hn, rfl⟩⟩, ?_⟩
      change a * j (algebraMap ℤ (NumberField.RingOfIntegers L) n) = j y
      rw [hjint]
      apply Subtype.ext
      change (a : AlgebraicClosure ℚ) * ((n : A) : AlgebraicClosure ℚ) = ((n • a : A) : AlgebraicClosure ℚ)
      rw [zsmul_eq_mul]
      push_cast
      ring
    · intro x y h
      exact ⟨1, by rw [hj_inj h]⟩
  -- the primes of `𝓞 L` over `p`
  intro P hP hpP
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdisjP : Disjoint ((Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers L) Mp :
      Submonoid _) : Set (NumberField.RingOfIntegers L)) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have hn' : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.mpr h)
    obtain ⟨α, β, hαβ⟩ := (Prime.coprime_iff_not_dvd hpr).mpr hn'
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : algebraMap ℤ (NumberField.RingOfIntegers L) (α * p + β * n) ∈ P := by
      rw [map_add, map_mul, map_mul]
      exact P.add_mem (P.mul_mem_left _ (by simpa using hpP)) (P.mul_mem_left _ hnP)
    rwa [hαβ, map_one] at this
  set P' : Ideal A := P.map (algebraMap (NumberField.RingOfIntegers L) A) with hP'
  have hP'p : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ A P hP hdisjP
  have hP'c : P'.comap (algebraMap (NumberField.RingOfIntegers L) A) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ A hP hdisjP
  have hL1 : IsLocalization.AtPrime (Localization.AtPrime P')
      (P'.comap (algebraMap (NumberField.RingOfIntegers L) A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers L) Mp) (Localization.AtPrime P') P'
  have hL2 : IsLocalization.AtPrime (Localization.AtPrime P') P := atPrime_congr hP'c
  let e : Localization.AtPrime P ≃ₐ[NumberField.RingOfIntegers L] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  have hFU5 : Algebra.FormallyUnramified A (Localization.AtPrime P') :=
    Algebra.FormallyUnramified.of_isLocalization P'.primeCompl
  haveI hTZ2 := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := A) (A := Localization.AtPrime P')
      (fun x => by simp only [eq_intCast, map_intCast])
  have hFU6 : Algebra.FormallyUnramified ℤ (Localization.AtPrime P') :=
    Algebra.FormallyUnramified.comp ℤ A _
  have hFU7 : Algebra.FormallyUnramified ℤ (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_equiv (A := Localization.AtPrime P')
      (AlgEquiv.ofRingEquiv (f := (e.symm : Localization.AtPrime P' ≃+* Localization.AtPrime P))
        (fun x => by simp only [eq_intCast, map_intCast]))
  have hfdL : FiniteDimensional ℚ L := finiteDimensional_residue E s₀ 𝔓 hU φ
  haveI : NumberField L := ⟨⟩
  have : Algebra.EssFiniteType ℤ (NumberField.RingOfIntegers L) := inferInstance
  have : Algebra.IsUnramifiedAt ℤ P := hFU7
  exact Ideal.ramificationIdx_eq_one P ℤ

end PropTSGlueDev4

#print axioms PropTSGlueDev4.snSpecializeUnram_aux
#print axioms PropTSGlueDev4.rbar_isLocalization
