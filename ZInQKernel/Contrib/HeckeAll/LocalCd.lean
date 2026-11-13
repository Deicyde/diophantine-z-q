import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# Mathlib's `L(C_d, s)` for every squarefree `d` (odd or even)

`ZInQKernel/RouteK/Rank/LFunctionCd.lean` computes Mathlib's L-function of
`C_d : y² = x³ − d² x` for odd squarefree `d`. This file removes the parity hypothesis.
The only new local input is at `p = 2` for even squarefree `d = 2e`: there `v₂(Δ) = 12`, so the
discriminant criterion for minimality does not apply. Instead we use `c₄`
(`isMinimal_baseChange_of_c₄`): for an integral model over `ℤ₂`, `c₄ = b₂² − 24 b₄` is a unit
if `a₁` is a unit and divisible by `16` otherwise, so `v₂(c₄) ∉ {1, 2, 3}`; since
`c₄(C_d) = 192 e²` has `v₂ = 6`, no change of variables with `v(u) > 0` keeps the model
integral.

## Main results

* `isMinimal_cdLocal'`: the model `y² = x³ − d² x` is minimal at every place, for squarefree `d`.
* `localPolynomial_cdLocal_eq'`: its local polynomial is `cdEulerPoly d p`.
* `LFunction_cd_apply_prime_pow'`, `LFunction_cd_apply'`, `LFunction_cd_apply_prime_eq_sub_card'`,
  `LFunction_cd_apply_prime_of_dvd'`, `LSeries_cd_eq'`: the statements of `LFunctionCd.lean`
  for every squarefree `d`.
-/

namespace ZInQ.Contrib.HeckeAll

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ZInQ.Literature

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

/-- **Minimality from `c₄`.** An integral model `W` is minimal if its `c₄` has no factorization
`r⁴ · c₄(W')` with `r ∈ 𝔪` and `W'` integral. -/
theorem isMinimal_baseChange_of_c₄ (W : WeierstrassCurve R)
    (h : ∀ r : R, r ∈ IsLocalRing.maximalIdeal R → ∀ W' : WeierstrassCurve R,
      W.c₄ ≠ r ^ 4 * W'.c₄) : IsMinimal R (W⁄K) := by
  have hI : IsIntegral R (W⁄K) := ⟨W, rfl⟩
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have hC' := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ, map_mul, map_pow]
  by_cases h' : vK (↑C.u⁻¹ : K) ≤ 1
  · exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le h')
  · exfalso
    replace h' := not_le.mp h'
    have hu : vK (C.u : K) < 1 := by
      have : (C.u : K) = (↑C.u⁻¹ : K)⁻¹ := by simp
      rw [this, map_inv₀]
      exact inv_lt_one_of_one_lt₀ h'
    obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
    rw [← hr, vK_algebraMap_lt_one_iff] at hu
    obtain ⟨W', hW'⟩ := hC'.integral
    apply h r hu W'
    apply IsFractionRing.injective R K
    have hc : (C • W⁄K).c₄ = algebraMap R K W'.c₄ := by
      rw [hW']; exact map_c₄ W' _
    have e1 : algebraMap R K W.c₄ = (W⁄K).c₄ := (map_c₄ W _).symm
    rw [variableChange_c₄] at hc
    rw [e1, map_mul, map_pow, hr, ← hc, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

end Generic

section Completion

open Rat.HeightOneSpectrum

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "Rv" => v.adicCompletionIntegers ℚ

theorem mem_maximalIdeal_iff_dvd (x : Rv) :
    x ∈ IsLocalRing.maximalIdeal Rv ↔ ((natGenerator v : ℕ) : Rv) ∣ x := by
  rw [maximalIdeal_eq_span, Ideal.mem_span_singleton]

/-- The `c₄` of an integral model over `ℤ₂`: if `a₁ ∈ 𝔪` then `16 ∣ c₄`, and otherwise `c₄ ∉ 𝔪`. -/
theorem c₄_two_adic (hv : natGenerator v = 2) (W : WeierstrassCurve Rv) :
    (∃ X : Rv, W.c₄ = 16 * X) ∨ W.c₄ ∉ IsLocalRing.maximalIdeal Rv := by
  have hm := mem_maximalIdeal_iff_dvd v
  rw [hv] at hm
  by_cases ha : W.a₁ ∈ IsLocalRing.maximalIdeal Rv
  · obtain ⟨t, ht⟩ := (hm _).mp ha
    left
    refine ⟨(t ^ 2 + W.a₂) ^ 2 - 3 * (W.a₄ + t * W.a₃), ?_⟩
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ht]
    push_cast; ring
  · right
    intro hc
    apply ha
    have hY : W.a₁ ^ 4 = W.c₄ - 2 * (4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄
        - 12 * W.a₁ * W.a₃) := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring
    have h4 : W.a₁ ^ 4 ∈ IsLocalRing.maximalIdeal Rv := by
      rw [hY]
      refine Ideal.sub_mem _ hc ((hm _).mpr ?_)
      exact ⟨4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₁ * W.a₃, by push_cast; ring⟩
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance 4 h4

theorem two_ne_zero_Rv : (2 : Rv) ≠ 0 := by
  intro h
  have := congrArg (ePadic v) h
  rw [map_ofNat, map_zero] at this
  exact two_ne_zero this

/-- **Minimality of `y² = x³ − d² x` at `2` for even squarefree `d`.** -/
theorem isMinimal_cdLocal_two {e : ℕ} (hv : natGenerator v = 2) (he : Odd e) :
    IsMinimal Rv (cdLocal v (2 * e)) := by
  rw [← cdModel_baseChange]
  apply isMinimal_baseChange_of_c₄
  intro r hr W' heq
  have hm := mem_maximalIdeal_iff_dvd v
  rw [hv] at hm
  have h3 : ((3 * e ^ 2 : ℕ) : Rv) ∉ IsLocalRing.maximalIdeal Rv := by
    rw [natCast_mem_maximalIdeal_iff, hv]
    intro h
    have : Odd (3 * e ^ 2) := (by decide : Odd 3).mul (he.pow)
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  have h16 : (16 : Rv) ≠ 0 := by
    have : (16 : Rv) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ (two_ne_zero_Rv v)
  have h4 : (4 : Rv) ≠ 0 := by
    have : (4 : Rv) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ (two_ne_zero_Rv v)
  obtain ⟨s, rfl⟩ := (hm r).mp hr
  rw [cdModel_c₄] at heq
  push_cast at heq
  -- `12 e² = s⁴ c₄'`
  have h12 : (12 : Rv) * (e : Rv) ^ 2 = s ^ 4 * W'.c₄ := by
    apply mul_left_cancel₀ h16
    linear_combination heq
  apply h3
  rcases c₄_two_adic v hv W' with ⟨X, hX⟩ | hc
  · rw [hX] at h12
    have : ((3 * e ^ 2 : ℕ) : Rv) = 2 * (2 * s ^ 4 * X) := by
      apply mul_left_cancel₀ h4
      push_cast
      linear_combination h12
    exact (hm _).mpr ⟨_, this⟩
  · have hs : s ∈ IsLocalRing.maximalIdeal Rv := by
      have hmem : s ^ 4 * W'.c₄ ∈ IsLocalRing.maximalIdeal Rv := by
        rw [← h12]
        exact (hm _).mpr ⟨6 * (e : Rv) ^ 2, by push_cast; ring⟩
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
      · exact Ideal.IsPrime.mem_of_pow_mem inferInstance 4 h
      · exact absurd h hc
    obtain ⟨s', rfl⟩ := (hm s).mp hs
    have : ((3 * e ^ 2 : ℕ) : Rv) = 2 * (2 * s' ^ 4 * W'.c₄) := by
      apply mul_left_cancel₀ h4
      push_cast
      linear_combination h12
    exact (hm _).mpr ⟨_, this⟩

/-- **The model `y² = x³ − d² x` is minimal at every place**, for squarefree `d`. -/
theorem isMinimal_cdLocal' {d : ℕ} (hsq : Squarefree d) : IsMinimal Rv (cdLocal v d) := by
  by_cases h2 : natGenerator v = 2 ∧ 2 ∣ d
  · obtain ⟨hv, e, rfl⟩ := h2
    have he : Odd e := by
      rw [← Nat.not_even_iff_odd]
      rintro ⟨f, rfl⟩
      have := hsq 2 ⟨f, by ring⟩
      exact absurd (Nat.isUnit_iff.mp this) (by norm_num)
    exact isMinimal_cdLocal_two v hv he
  · rw [← cdModel_baseChange]
    apply isMinimal_baseChange_of_notMem
    rw [cdModel_Δ, ← Nat.cast_pow, ← Int.cast_natCast, intCast_mem_maximalIdeal_pow_iff]
    intro h
    have hp := prime_natGenerator v
    have h' : (natGenerator v ^ 2) ^ 6 ∣ (2 * d) ^ 6 := by
      rw [← pow_mul]; exact_mod_cast h
    rw [Nat.pow_dvd_pow_iff (by norm_num)] at h'
    by_cases hv : natGenerator v = 2
    · have hd : ¬ 2 ∣ d := fun hd => h2 ⟨hv, hd⟩
      rw [hv] at h'
      obtain ⟨k, hk⟩ := h'
      exact hd ⟨k, by omega⟩
    · have hcop : Nat.Coprime (natGenerator v ^ 2) 2 :=
        Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hv)
      have := hsq (natGenerator v) (by rw [← pow_two]; exact hcop.dvd_of_dvd_mul_left h')
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

/-- Additive reduction at `v ∣ 2d`, for squarefree `d`. -/
theorem hasAdditiveReduction_cdLocal' {d : ℕ} (hsq : Squarefree d)
    (hp : natGenerator v ∣ 2 * d) : HasAdditiveReduction Rv (cdLocal v d) := by
  refine (hasAdditiveReduction_iff _ _).mpr ⟨isMinimal_cdLocal' v hsq, ?_, ?_⟩
  · rw [cdLocal_Δ_eq, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact Ideal.pow_mem_of_mem _ ((natCast_mem_maximalIdeal_iff v _).mpr hp) 6 (by norm_num)
  · rw [cdLocal_c₄_eq, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact (natCast_mem_maximalIdeal_iff v _).mpr (hp.trans ⟨24 * d, by ring⟩)

theorem localPolynomial_cdLocal_of_dvd' {d : ℕ} (hsq : Squarefree d)
    (hp : natGenerator v ∣ 2 * d) : (cdLocal v d).localPolynomial Rv = 1 := by
  have := hasAdditiveReduction_cdLocal' v hsq hp
  exact localPolynomial_of_hasAdditiveReduction _ (cdLocal_Δ_ne_zero v hsq.ne_zero)

theorem localPolynomial_cdLocal_eq' {d : ℕ} (hsq : Squarefree d) :
    (cdLocal v d).localPolynomial Rv = cdEulerPoly d (natGenerator v) := by
  unfold cdEulerPoly
  split_ifs with h
  · exact localPolynomial_cdLocal_of_dvd' v hsq h
  · exact localPolynomial_cdLocal_of_not_dvd v h

end Completion

section LFunction

open ArithmeticFunction Rat.HeightOneSpectrum

/-- **The Dirichlet coefficient of `L(C_d, s)` at `p ^ k`**, for every squarefree `d`. -/
theorem LFunction_cd_apply_prime_pow' {d : ℕ} (hsq : Squarefree d) (p : ℕ)
    [hp' : Fact p.Prime] (k : ℕ) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) := by
  classical
  have hp := hp'.out
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  set q := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) with hq_def
  set F := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    (cdLocal w d).localPowerSeries (w.adicCompletionIntegers ℚ) with hF_def
  have hF : ∀ w, PowerSeries.constantCoeff (F w) = 1 := fun w => by
    simp [F, localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  have hf1 : ∀ w, ofPowerSeries (q w) (F w) 1 = 1 := fun w => by
    rw [ofPowerSeries_apply_one, hF]
  have hvan : ∀ w, w ≠ v → ∀ m, m ∣ natGenerator v ^ k → m ≠ 1 →
      ofPowerSeries (q w) (F w) m = 0 := by
    intro w hw m hm hm1
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
    have hqw : q w = natGenerator w := natCard_residueField w
    rw [hqw, ofPowerSeries_apply (prime_natGenerator w).one_lt, Function.extend_apply']
    · rfl
    rintro ⟨l, hl⟩
    rcases j with _ | j
    · exact hm1 (pow_zero _)
    rcases l with _ | l
    · exact (Nat.one_lt_pow (Nat.succ_ne_zero j) hp.one_lt).ne (by simpa using hl)
    · have hdvd : natGenerator w ∣ natGenerator v ^ (j + 1) :=
        hl ▸ dvd_pow_self _ (Nat.succ_ne_zero l)
      exact hw (natGenerator_injective ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hp).mp
        ((prime_natGenerator w).dvd_of_dvd_pow hdvd)))
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp
    (tendsTo_eulerProduct_ofPowerSeries q F hF (natGenerator v ^ k))
  have key := hs0 (insert v s0) (Finset.subset_insert _ _)
  change eulerProduct (fun w => ofPowerSeries (q w) (F w)) (natGenerator v ^ k) = _
  have hrest := prod_vanish (fun w => ofPowerSeries (q w) (F w)) (natGenerator v ^ k)
    ((insert v s0).erase v) fun w hw => ⟨hf1 w, hvan w (Finset.ne_of_mem_erase hw)⟩
  rw [← key, ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v s0), mul_comm,
    mul_apply_of_vanish hrest.1 hrest.2]
  have hq : q v = natGenerator v := natCard_residueField v
  rw [hq, ofPowerSeries_apply_pow hp.one_lt]
  simp only [F, localPowerSeries]
  rw [localPolynomial_cdLocal_eq' v hsq]

theorem LFunction_cd_apply_prime' {d : ℕ} (hsq : Squarefree d) (p : ℕ) [Fact p.Prime] :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      if p ∣ 2 * d then 0
      else (p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point := by
  have h := LFunction_cd_apply_prime_pow' hsq p 1
  rw [pow_one] at h
  rw [h, coeff_one_invOfUnit _ (cdEulerPoly_coeff_zero d p), ← cdModel_eq_shortCurve]
  unfold cdEulerPoly
  split_ifs <;> simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]

/-- **`L(C_d, s)` in full**, for every squarefree `d`. -/
theorem LFunction_cd_apply' {d : ℕ} (hsq : Squarefree d) {n : ℕ} (hn : n ≠ 0) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction n = n.factorization.prod fun p k =>
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) := by
  rw [(isMultiplicative_LFunction _).multiplicative_factorization _ hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)⟩
  exact LFunction_cd_apply_prime_pow' hsq p _

theorem LFunction_cd_apply_prime_eq_sub_card' {d : ℕ} (hsq : Squarefree d) (p : ℕ)
    [Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      p - Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  rw [LFunction_cd_apply_prime' hsq p]
  simp only [hp, ↓reduceIte]
  rw [natCard_point_shortCurve_zmod p hp]
  push_cast; ring

theorem LFunction_cd_apply_prime_of_dvd' {d : ℕ} (hsq : Squarefree d) (p : ℕ)
    [Fact p.Prime] (hp : p ∣ 2 * d) : (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 := by
  rw [LFunction_cd_apply_prime' hsq p]
  simp only [hp, ↓reduceIte]

/-- **Mathlib's `L(C_d, s)` is the standard Euler product**, for every squarefree `d`. -/
theorem LSeries_cd_eq' {d : ℕ} (hsq : Squarefree d) (s : ℂ) :
    (shortCurve (-(d : ℚ) ^ 2)).LSeries s = LSeries (fun n => (cdCoeff d n : ℂ)) s := by
  refine LSeries_congr (fun {n} hn => ?_) s
  simp only [Function.comp_apply, cdCoeff, hn, ↓reduceIte, LFunction_cd_apply' hsq hn]

end LFunction

end ZInQ.Contrib.HeckeAll
