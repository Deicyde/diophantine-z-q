import ZInQKernel.Multiplication.Completeness.TwoSlope

/-!
# Lemma P: poles at an old prime are absorbed by the witness `q`

Route AP of `docs/research/nt-22p.md`, §3.2. Let `ℓ` be a prime and `t = u/v` in lowest terms
with `e = v_ℓ(v) ≥ 1` (and `e ≥ 3` if `ℓ = 2`), such that the seven numbers `u - c v`
(`c ∈ 𝒞 ∪ {1}`) are prime to `ℓ` (`PoleAbsorbHyp ℓ t`). Then, for `R₀ = F(t)/(t - 1)⁸`
(the value of `slopeR0` at `η = 1`):

1. `v_ℓ(R₀) = 2e`, `v_ℓ(t - 1) = -e`, and `R₀` is a square in `ℚ_ℓ` (`lemmaP_one`);
2. for every `N` the set of `q ∈ ℚ_ℓ` with `‖1 - R₀ q²‖ ≤ ℓ^{-N}` (that is, `v_ℓ(1 - R₀q²) ≥ N`)
   is a non-empty open set (`lemmaP_two`), and it contains a rational ball around a rational
   centre `m / ℓ^k` (`lemmaP_two_ball`), which is the form the weak approximation step uses.

The note also assumes `F(t) > 0`; that assumption only fixes the sign `η = 1` of the slope
predicate and is not needed for these statements (they are about `slopeR0 1 t`).

The square root comes from Hensel's lemma for `Y² - X` in `ℤ_[ℓ]`, where
`X = ∏_{c ∈ 𝒞} (u - c v) ≡ u⁶ (mod ℓ^e)`.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- The hypotheses of Lemma P at the prime `ℓ`, for `t = u/v` in lowest terms (`u = t.num`,
`v = t.den`): `e = v_ℓ(v) ≥ 1`, `e ≥ 3` if `ℓ = 2`, and the seven numbers `u - c v`,
`c ∈ 𝒞 ∪ {1}` (`patternShifts`), are prime to `ℓ`. -/
def PoleAbsorbHyp (ℓ : ℕ) (t : ℚ) : Prop :=
  1 ≤ padicValNat ℓ t.den ∧ (ℓ = 2 → 3 ≤ padicValNat ℓ t.den) ∧
    ∀ c ∈ patternShifts, ¬ (ℓ : ℤ) ∣ t.num - c * t.den

/-- The contact numerator `F(u, v) = ∏_{c ∈ 𝒞} (u - c v)`. -/
def apContactNum (u v : ℤ) : ℤ :=
  (u - 0 * v) * (u - (-15) * v) * (u - (-20) * v) * (u - (-24) * v) * (u - (-30) * v) *
    (u - (-60) * v)

theorem apContactNum_dvd (u v : ℤ) : v ∣ apContactNum u v - u ^ 6 := by
  have h : ∀ c : ℤ, u - c * v ≡ u [ZMOD v] := fun c => by
    rw [Int.modEq_iff_dvd]; exact ⟨c, by ring⟩
  have := (((((h 0).mul (h (-15))).mul (h (-20))).mul (h (-24))).mul (h (-30))).mul (h (-60))
  have h2 := this.symm.dvd
  rw [show u ^ 6 = u * u * u * u * u * u by ring]
  exact h2

/-- `F(t)/(t - 1)⁸ = F(u, v) v² / (u - v)⁸` for `t = u/v`. -/
theorem contactQuot_apContactNum {u v : ℤ} (hv : v ≠ 0) (hu1 : u - v ≠ 0) :
    contactPoly ((u : ℚ) / v) / ((u : ℚ) / v - 1) ^ 8 =
      (apContactNum u v : ℚ) * (v : ℚ) ^ 2 / ((u - v : ℤ) : ℚ) ^ 8 := by
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv
  have hu1' : (u : ℚ) - v ≠ 0 := by
    have : ((u - v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu1
    push_cast at this; exact this
  rw [show (u : ℚ) / v - 1 = ((u : ℚ) - v) / v by field_simp]
  unfold contactPoly apContactNum
  push_cast
  field_simp
  ring

/-- The non-divisibility facts behind `PoleAbsorbHyp`, in the explicit form. -/
theorem PoleAbsorbHyp.not_dvd {ℓ : ℕ} {t : ℚ} (hP : PoleAbsorbHyp ℓ t) :
    (∀ c ∈ contactInts, ¬ (ℓ : ℤ) ∣ t.num - c * t.den) ∧ ¬ (ℓ : ℤ) ∣ t.num - t.den := by
  refine ⟨fun c hc => hP.2.2 c (contactInts_sub_patternShifts hc), ?_⟩
  have := hP.2.2 1 (by simp [patternShifts])
  simpa using this

theorem not_dvd_apContactNum {ℓ : ℕ} (hℓ : ℓ.Prime) {u v : ℤ}
    (h : ∀ c ∈ contactInts, ¬ (ℓ : ℤ) ∣ u - c * v) : ¬ (ℓ : ℤ) ∣ apContactNum u v := by
  have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  unfold apContactNum
  simp only [hℓ'.dvd_mul]
  rintro (((((h0 | h0) | h0) | h0) | h0) | h0)
  · exact h 0 (by simp [contactInts]) h0
  · exact h (-15) (by simp [contactInts]) h0
  · exact h (-20) (by simp [contactInts]) h0
  · exact h (-24) (by simp [contactInts]) h0
  · exact h (-30) (by simp [contactInts]) h0
  · exact h (-60) (by simp [contactInts]) h0

theorem norm_intCast_eq_one_of_not_dvd {ℓ : ℕ} [Fact ℓ.Prime] {u : ℤ} (hu : ¬ (ℓ : ℤ) ∣ u) :
    ‖(u : ℤ_[ℓ])‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun h => hu ((PadicInt.norm_int_lt_one_iff_dvd u).mp h))

/-- **Hensel step.** If `ℓ^e ∣ v` with `e ≥ 1` (`e ≥ 3` for `ℓ = 2`) and `ℓ ∤ u`, then
`F(u, v)` is a square in `ℤ_[ℓ]`. -/
theorem exists_sqrt_apContactNum {ℓ : ℕ} [Fact ℓ.Prime] {u v : ℤ} {e : ℕ}
    (he : (ℓ : ℤ) ^ e ∣ v) (he1 : 1 ≤ e) (he2 : ℓ = 2 → 3 ≤ e) (hu : ¬ (ℓ : ℤ) ∣ u) :
    ∃ z : ℤ_[ℓ], z ^ 2 = (apContactNum u v : ℤ_[ℓ]) := by
  set X := apContactNum u v with hX
  set F : Polynomial ℤ_[ℓ] := Polynomial.X ^ 2 - Polynomial.C (X : ℤ_[ℓ]) with hF
  have hFa : Polynomial.aeval ((u : ℤ_[ℓ]) ^ 3) F = ((u ^ 6 - X : ℤ) : ℤ_[ℓ]) := by
    simp only [hF, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    push_cast; simp; ring
  have hF'a : Polynomial.aeval ((u : ℤ_[ℓ]) ^ 3) (Polynomial.derivative F) =
      ((2 * u ^ 3 : ℤ) : ℤ_[ℓ]) := by
    simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C, sub_zero]
    simp
  have hn1 : ‖((u ^ 6 - X : ℤ) : ℤ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := by
    rw [PadicInt.norm_int_le_pow_iff_dvd]
    have h1 := he.trans (apContactNum_dvd u v)
    have : u ^ 6 - X = -(X - u ^ 6) := by ring
    rw [this]
    exact h1.neg_right
  have hu1 := norm_intCast_eq_one_of_not_dvd hu
  have hn2 : ‖((2 * u ^ 3 : ℤ) : ℤ_[ℓ])‖ = ‖(2 : ℤ_[ℓ])‖ := by
    push_cast; rw [norm_mul, norm_pow, hu1]; simp
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  have hnorm : ‖Polynomial.aeval ((u : ℤ_[ℓ]) ^ 3) F‖ <
      ‖Polynomial.aeval ((u : ℤ_[ℓ]) ^ 3) (Polynomial.derivative F)‖ ^ 2 := by
    rw [hFa, hF'a, hn2]
    refine lt_of_le_of_lt hn1 ?_
    by_cases h2 : ℓ = 2
    · subst h2
      have h22 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
        have := PadicInt.norm_p (p := 2)
        push_cast at this; rw [this]; norm_num
      rw [h22]
      have h3 := he2 rfl
      calc ((2 : ℕ) : ℝ) ^ (-(e : ℤ)) ≤ ((2 : ℕ) : ℝ) ^ (-3 : ℤ) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ < (1 / 2) ^ 2 := by norm_num
    · have h21 : ‖(2 : ℤ_[ℓ])‖ = 1 := by
        have : ¬ (ℓ : ℤ) ∣ 2 := by
          intro hd
          have := Int.le_of_dvd (by norm_num) hd
          have h2' := (Fact.out : ℓ.Prime).two_le
          have : ℓ = 2 := by omega
          exact h2 this
        have := norm_intCast_eq_one_of_not_dvd (ℓ := ℓ) this
        simpa using this
      rw [h21, one_pow]
      calc (ℓ : ℝ) ^ (-(e : ℤ)) ≤ (ℓ : ℝ) ^ (-1 : ℤ) :=
            zpow_le_zpow_right₀ hℓ1.le (by omega)
        _ < 1 := by
          rw [zpow_neg_one]; exact inv_lt_one_of_one_lt₀ hℓ1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  simp only [hF, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hz
  simp at hz
  linear_combination hz

/-- Data of `t` under `PoleAbsorbHyp`: `t = u/v` with `u = t.num`, `v = t.den`, `u ≠ v`. -/
theorem PoleAbsorbHyp.num_sub_den_ne_zero {ℓ : ℕ} {t : ℚ} (hP : PoleAbsorbHyp ℓ t) :
    t.num - (t.den : ℤ) ≠ 0 := by
  intro h
  apply hP.not_dvd.2
  rw [h]; exact dvd_zero _

theorem eq_num_div_den (t : ℚ) : t = ((t.num : ℤ) : ℚ) / ((t.den : ℤ) : ℚ) := by
  push_cast; exact (Rat.num_div_den t).symm

/-- **Lemma P, part (1).** Under `PoleAbsorbHyp ℓ t`, with `e = v_ℓ(den t)`:
`v_ℓ(R₀) = 2e`, `v_ℓ(t - 1) = -e`, and `R₀ = F(t)/(t - 1)⁸` is a square in `ℚ_ℓ`. -/
theorem lemmaP_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {t : ℚ} (hP : PoleAbsorbHyp ℓ t) :
    padicValRat ℓ (slopeR0 1 t) = 2 * (padicValNat ℓ t.den : ℤ) ∧
    padicValRat ℓ (t - 1) = -(padicValNat ℓ t.den : ℤ) ∧
    ∃ z : ℚ_[ℓ], ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) = z ^ 2 := by
  set u : ℤ := t.num with hu
  set v : ℤ := (t.den : ℤ) with hv
  set e : ℕ := padicValNat ℓ t.den with he
  have hv0 : v ≠ 0 := by rw [hv]; exact_mod_cast t.den_nz
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast hv0
  have htuv : t = (u : ℚ) / v := eq_num_div_den t
  have hu1 : u - v ≠ 0 := hP.num_sub_den_ne_zero
  have hu1Q : ((u - v : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu1
  obtain ⟨hnd, hnd1⟩ := hP.not_dvd
  have hX := not_dvd_apContactNum hℓ.out hnd
  have hX0 : apContactNum u v ≠ 0 := fun h => hX (by rw [h]; exact dvd_zero _)
  have hXQ : (apContactNum u v : ℚ) ≠ 0 := by exact_mod_cast hX0
  have hR0 : slopeR0 1 t = (apContactNum u v : ℚ) * (v : ℚ) ^ 2 / ((u - v : ℤ) : ℚ) ^ 8 := by
    rw [slopeR0, one_mul, htuv]
    exact contactQuot_apContactNum hv0 hu1
  have hvv : padicValRat ℓ (v : ℚ) = e := by
    rw [hv, padicValRat.of_int, padicValInt.of_nat]
  have hv1 : padicValRat ℓ ((u - v : ℤ) : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnd1]; rfl
  have hvX : padicValRat ℓ (apContactNum u v : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hX]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hR0, padicValRat.div (mul_ne_zero hXQ (pow_ne_zero _ hvQ)) (pow_ne_zero _ hu1Q),
      padicValRat.mul hXQ (pow_ne_zero _ hvQ), padicValRat.pow, padicValRat.pow,
      hvv, hv1, hvX]
    push_cast; ring
  · have : t - 1 = ((u - v : ℤ) : ℚ) / v := by rw [htuv]; push_cast; field_simp
    rw [this, padicValRat.div hu1Q hvQ, hvv, hv1]; ring
  · have hdvd : (ℓ : ℤ) ^ e ∣ v := by
      rw [hv]; exact_mod_cast pow_padicValNat_dvd
    have hu0 : ¬ (ℓ : ℤ) ∣ u := by
      have := hnd 0 (by simp [contactInts]); simpa using this
    obtain ⟨z, hz⟩ := exists_sqrt_apContactNum hdvd hP.1 hP.2.1 hu0
    have hzQ : (z : ℚ_[ℓ]) ^ 2 = ((apContactNum u v : ℤ) : ℚ_[ℓ]) := by
      have := congrArg (fun y : ℤ_[ℓ] => (y : ℚ_[ℓ])) hz
      simpa using this
    have hu1P : ((u - v : ℤ) : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hu1
    refine ⟨(v : ℚ_[ℓ]) * (z : ℚ_[ℓ]) / ((u - v : ℤ) : ℚ_[ℓ]) ^ 4, ?_⟩
    rw [hR0]
    push_cast
    rw [div_pow, mul_pow, ← pow_mul, show (z : ℚ_[ℓ]) ^ 2 = _ from hzQ]
    push_cast
    ring

/-- Every `ℓ`-adic number is approximated by rationals `m / ℓ^k`. -/
theorem exists_int_div_pow_near {p : ℕ} [hp : Fact p.Prime] (x : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℤ) (k : ℕ), ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ < ε := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖x‖ hp1
  have hpk : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hnpk : ‖(p : ℚ_[p]) ^ k‖ = ((p : ℝ) ^ k)⁻¹ := by
    rw [Padic.norm_p_pow, zpow_neg, zpow_natCast]
  have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by linarith) _
  set y : ℚ_[p] := (p : ℚ_[p]) ^ k * x with hy
  have hy1 : ‖y‖ ≤ 1 := by
    rw [hy, norm_mul, hnpk, inv_mul_le_iff₀ hpkpos, mul_one]; exact hk.le
  obtain ⟨m, hm⟩ := PadicInt.denseRange_intCast.exists_dist_lt (Padic.lift y hy1)
    (show 0 < ε / (p : ℝ) ^ k from div_pos hε hpkpos)
  refine ⟨m, k, ?_⟩
  have hm' : ‖y - (m : ℚ_[p])‖ < ε / (p : ℝ) ^ k := by
    rw [dist_eq_norm, PadicInt.norm_def] at hm
    simpa using hm
  have : x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k = (y - m) / (p : ℚ_[p]) ^ k := by
    rw [hy]; field_simp
  rw [this, norm_div, hnpk, div_inv_eq_mul]
  rwa [lt_div_iff₀ hpkpos] at hm'

/-- The core of Lemma P(2): if `R₀ w² = 1` in `ℚ_ℓ` and `‖q - w‖ ≤ ‖w‖ ℓ^{-N}` (and
`‖q - w‖ ≤ ‖w‖`), then `‖1 - R₀ q²‖ ≤ ℓ^{-N}`. -/
theorem norm_one_sub_le_of_near {p : ℕ} [hp : Fact p.Prime] {R w q : ℚ_[p]} (hw : R * w ^ 2 = 1)
    {r : ℝ} (h1 : ‖q - w‖ ≤ ‖w‖) (h2 : ‖q - w‖ ≤ ‖w‖ * r) : ‖1 - R * q ^ 2‖ ≤ r := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hR : ‖R‖ = (‖w‖ ^ 2)⁻¹ := by
    have := congrArg norm hw
    rw [norm_mul, norm_pow, norm_one] at this
    field_simp; linarith
  have he : 1 - R * q ^ 2 = R * (w - q) * (w + q) := by linear_combination -hw
  have hplus : ‖w + q‖ ≤ ‖w‖ := by
    have : w + q = (q - w) + 2 * w := by ring
    rw [this]
    refine (Padic.nonarchimedean _ _).trans (max_le h1 ?_)
    rw [norm_mul]
    have : ‖(2 : ℚ_[p])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := p) 2
      simpa using this
    nlinarith [norm_nonneg w]
  have hr : 0 ≤ r := (mul_nonneg_iff_of_pos_left hwn).mp (le_trans (norm_nonneg _) h2)
  rw [he, norm_mul, norm_mul, hR, norm_sub_rev]
  calc (‖w‖ ^ 2)⁻¹ * ‖q - w‖ * ‖w + q‖ ≤ (‖w‖ ^ 2)⁻¹ * (‖w‖ * r) * ‖w‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) hplus (norm_nonneg _)
          (mul_nonneg (by positivity) (mul_nonneg hwn.le hr))
    _ = r := by field_simp

/-- **Lemma P, part (2).** Under `PoleAbsorbHyp ℓ t`, for every `N ∈ ℤ` the set of `x ∈ ℚ_ℓ`
with `‖1 - R₀ x²‖ ≤ ℓ^{-N}` (that is, `v_ℓ(1 - R₀ x²) ≥ N`) is non-empty and open. -/
theorem lemmaP_two {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {t : ℚ} (hP : PoleAbsorbHyp ℓ t) (N : ℤ) :
    {x : ℚ_[ℓ] | ‖1 - ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) * x ^ 2‖ ≤ (ℓ : ℝ) ^ (-N)}.Nonempty ∧
    IsOpen {x : ℚ_[ℓ] | ‖1 - ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) * x ^ 2‖ ≤ (ℓ : ℝ) ^ (-N)} := by
  obtain ⟨-, -, z, hz⟩ := lemmaP_one hP
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hz0 : z ≠ 0 := by
    rintro rfl
    have hR0 : slopeR0 1 t ≠ 0 := by
      have := (lemmaP_one hP).1
      intro h; rw [h, padicValRat.zero] at this
      have := hP.1; omega
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
    exact hR0 (by exact_mod_cast hz)
  refine ⟨⟨z⁻¹, ?_⟩, ?_⟩
  · show ‖1 - ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) * z⁻¹ ^ 2‖ ≤ _
    rw [hz, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz0), sub_self, norm_zero]
    positivity
  · have : {x : ℚ_[ℓ] | ‖1 - ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) * x ^ 2‖ ≤ (ℓ : ℝ) ^ (-N)} =
        (fun x : ℚ_[ℓ] => 1 - ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) * x ^ 2) ⁻¹'
          Metric.closedBall 0 ((ℓ : ℝ) ^ (-N)) := by
      ext x; simp
    rw [this]
    exact (IsUltrametricDist.isOpen_closedBall _ (by positivity)).preimage (by fun_prop)

/-- **Lemma P, part (2), rational form.** Under `PoleAbsorbHyp ℓ t`, for every `N ∈ ℤ` there are
a centre `m / ℓ^k` and a radius `ℓ^{-M}` such that every rational `q` in the ball has
`|1 - R₀ q²|_ℓ ≤ ℓ^{-N}`. -/
theorem lemmaP_two_ball {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {t : ℚ} (hP : PoleAbsorbHyp ℓ t) (N : ℤ) :
    ∃ (m : ℤ) (k M : ℕ), ∀ q : ℚ, padicNorm ℓ (q - m / (ℓ : ℚ) ^ k) ≤ (ℓ : ℚ) ^ (-(M : ℤ)) →
      padicNorm ℓ (slopeA (slopeR0 1 t) q) ≤ (ℓ : ℚ) ^ (-N) := by
  obtain ⟨-, -, z, hz⟩ := lemmaP_one hP
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hR0 : slopeR0 1 t ≠ 0 := by
    have := (lemmaP_one hP).1
    intro h; rw [h, padicValRat.zero] at this
    have := hP.1; omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
    exact hR0 (by exact_mod_cast hz)
  set w : ℚ_[ℓ] := z⁻¹ with hw
  have hRw : ((slopeR0 1 t : ℚ) : ℚ_[ℓ]) * w ^ 2 = 1 := by
    rw [hz, hw, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz0)]
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (inv_ne_zero hz0)
  set ρ : ℝ := min ‖w‖ (‖w‖ * (ℓ : ℝ) ^ (-N)) with hρ
  have hρpos : 0 < ρ := lt_min hwn (by positivity)
  obtain ⟨m, k, hmk⟩ := exists_int_div_pow_near w hρpos
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hρpos (inv_lt_one_of_one_lt₀ hℓ1)
  refine ⟨m, k, M, fun q hq => ?_⟩
  -- transport to `ℚ_ℓ`
  have hq' : ‖(q : ℚ_[ℓ]) - (m : ℚ_[ℓ]) / (ℓ : ℚ_[ℓ]) ^ k‖ ≤ ρ := by
    have h1 : ‖(q : ℚ_[ℓ]) - (m : ℚ_[ℓ]) / (ℓ : ℚ_[ℓ]) ^ k‖ =
        (padicNorm ℓ (q - m / (ℓ : ℚ) ^ k) : ℝ) := by
      rw [← Padic.eq_padicNorm]; push_cast; rfl
    rw [h1]
    refine le_trans ?_ hM.le
    have h2 : ((padicNorm ℓ (q - m / (ℓ : ℚ) ^ k) : ℚ) : ℝ) ≤ (((ℓ : ℚ) ^ (-(M : ℤ)) : ℚ) : ℝ) := by
      exact_mod_cast hq
    refine h2.trans (le_of_eq ?_)
    push_cast
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hqw : ‖(q : ℚ_[ℓ]) - w‖ ≤ ρ := by
    have : (q : ℚ_[ℓ]) - w = ((q : ℚ_[ℓ]) - (m : ℚ_[ℓ]) / (ℓ : ℚ_[ℓ]) ^ k) +
        ((m : ℚ_[ℓ]) / (ℓ : ℚ_[ℓ]) ^ k - w) := by ring
    rw [this]
    refine (Padic.nonarchimedean _ _).trans (max_le hq' ?_)
    rw [norm_sub_rev]; exact hmk.le
  have key := norm_one_sub_le_of_near hRw (hqw.trans (min_le_left _ _))
    (hqw.trans (min_le_right _ _))
  have h3 : ((padicNorm ℓ (slopeA (slopeR0 1 t) q) : ℚ) : ℝ) ≤ (ℓ : ℝ) ^ (-N) := by
    rw [← Padic.eq_padicNorm, slopeA]; push_cast; exact key
  have h4 : (((ℓ : ℚ) ^ (-N) : ℚ) : ℝ) = (ℓ : ℝ) ^ (-N) := by push_cast; rfl
  rw [← h4] at h3
  exact_mod_cast h3

/-- **Lemma P, part (2), as stated in the note.** For every `N` there is a rational `q₀` with
`v_ℓ(1 - R₀ q₀²) ≥ N`, in the form `|1 - R₀ q₀²|_ℓ ≤ ℓ^{-N}` (which also covers the case
`1 - R₀ q₀² = 0`, of valuation `∞`). -/
theorem lemmaP_two_rat {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ} (hP : PoleAbsorbHyp ℓ t) (N : ℤ) :
    ∃ q₀ : ℚ, padicNorm ℓ (slopeA (slopeR0 1 t) q₀) ≤ (ℓ : ℚ) ^ (-N) := by
  obtain ⟨m, k, M, h⟩ := lemmaP_two_ball hP N
  exact ⟨m / (ℓ : ℚ) ^ k, h _ (by simp)⟩

end ZInQ.Mult
