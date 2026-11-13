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
  sorry

end PropTSGlueDev4
