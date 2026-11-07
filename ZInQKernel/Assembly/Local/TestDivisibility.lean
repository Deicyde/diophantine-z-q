import ZInQKernel.Assembly.Local.FormalMultiplication
import ZInQKernel.Assembly.Local.SixLocalTests
import ZInQKernel.Assembly.Local.PoleObstruction
import ZInQKernel.Compiler.Precision.Relation

/-!
# Divisibility from the six local tests

Blueprint: `assembly/local-tests/test-divisibility.md` (Lemma 11.1).

If `Test(n, κ, t)` holds then `M_{S_ht}(t) ∣ κ F(n)` (`test_dvd`), where `M_{S_ht}(t)` is
`contactSupport heightPrimes t`. No hypothesis is used.

For a prime `p > 324` with `δ = v_p(t - c) > 0` odd (`prime_dvd_of_test`): `v_p(F(t)) = δ`
(`contact_val`), `v_p(R) = δ + 2b` with `b ≤ 0` (`testR_val`); the pole obstruction and the
trace bound at a prime `π ∣ p` where `v_π(W)` is maximal give `v_π(D_j) ≥ 1` for all six tests
(`tests_small`); the first four put `H, U` in `E₁(π)` and `V₀, V₁` in `E₁(σπ)`, and the last two,
through multiplication in the formal group (`ratio_congr`), give `s₀ ≡ th` and
`s₀ - κn ≡ t(h - κ)` modulo `p`, hence `p ∣ κ(n - c)`.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult ZInQ.Compiler.Precision

/-! ### Valuations at the primes above an odd prime -/

section Primes

variable {p : ℕ} [Fact p.Prime] {π : Zs}

theorem vP_ratCast (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {x : ℚ} (hx : x ≠ 0) :
    vP π hπ (x : K0) = ((padicValRat p x : ℤ) : WithTop ℤ) := by
  rw [vP_apply hπ (Rat.cast_ne_zero.mpr hx), Mult.vp_ratCast hp2 hπ hπp]

theorem vge_ratCast_iff (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) (k : ℤ) (x : ℚ) :
    Vge (vP π hπ) k (x : K0) ↔ x = 0 ∨ k ≤ padicValRat p x := by
  rw [Vge, le_vP_iff, Rat.cast_eq_zero, Mult.vp_ratCast hp2 hπ hπp]

theorem dvd_of_vge_intCast (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {m : ℤ}
    (h : Vge (vP π hπ) 1 (m : K0)) : (p : ℤ) ∣ m := by
  rw [← Rat.cast_intCast, vge_ratCast_iff hp2 hπ hπp] at h
  rcases h with h0 | h1
  · rw [Int.cast_eq_zero] at h0; rw [h0]; exact dvd_zero _
  · rw [padicValRat.of_int] at h1
    have := (padicValInt_dvd_iff 1 m).mpr (Or.inr (by exact_mod_cast h1))
    simpa using this

theorem vge_star_iff (hπ : Prime π) (k : ℤ) (y : K0) :
    Vge (vP (star π) (prime_star hπ)) k y ↔ Vge (vP π hπ) k (star y) := by
  rw [Vge, Vge, vP_star]

theorem vge_star_ratCast_iff (hπ : Prime π) (k : ℤ) (x : ℚ) :
    Vge (vP (star π) (prime_star hπ)) k (x : K0) ↔ Vge (vP π hπ) k (x : K0) := by
  rw [vge_star_iff, star_ratCast]

end Primes

/-! ### Contact values -/

theorem contactSet_int {c : ℚ} (hc : c ∈ contactSet) :
    ∃ a : ℤ, (a : ℚ) = c ∧ -60 ≤ a ∧ a ≤ 0 ∧ ∀ n : ℤ, (n - a) ∣ sixF n := by
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, by norm_num, le_rfl, fun n =>
      ⟨(n + 15) * (n + 20) * (n + 24) * (n + 30) * (n + 60), by simp only [sixF]; ring⟩⟩
  · exact ⟨-15, by norm_num, by norm_num, by norm_num, fun n =>
      ⟨n * (n + 20) * (n + 24) * (n + 30) * (n + 60), by simp only [sixF]; ring⟩⟩
  · exact ⟨-20, by norm_num, by norm_num, by norm_num, fun n =>
      ⟨n * (n + 15) * (n + 24) * (n + 30) * (n + 60), by simp only [sixF]; ring⟩⟩
  · exact ⟨-24, by norm_num, by norm_num, by norm_num, fun n =>
      ⟨n * (n + 15) * (n + 20) * (n + 30) * (n + 60), by simp only [sixF]; ring⟩⟩
  · exact ⟨-30, by norm_num, by norm_num, by norm_num, fun n =>
      ⟨n * (n + 15) * (n + 20) * (n + 24) * (n + 60), by simp only [sixF]; ring⟩⟩
  · exact ⟨-60, by norm_num, by norm_num, by norm_num, fun n =>
      ⟨n * (n + 15) * (n + 20) * (n + 24) * (n + 30), by simp only [sixF]; ring⟩⟩

/-- If `δ = v_p(t - c) > 0` for a contact value `c` and `p > 60`, then `v_p(F(t)) = δ`. -/
theorem contact_val {p : ℕ} [Fact p.Prime] (hp : 60 < p) {t c : ℚ} (hc : c ∈ contactSet)
    (ht : t ∉ contactSet) (hpos : 0 < padicValRat p (t - c)) :
    padicValRat p (contactPoly t) = padicValRat p (t - c) := by
  classical
  rw [contactPoly_eq_prod, ← Finset.mul_prod_erase _ _ hc]
  have htc0 : t - c ≠ 0 := sub_ne_zero.mpr fun h => ht (h ▸ hc)
  have hunit : ∀ c' ∈ contactSet.erase c, t - c' ≠ 0 ∧ padicValRat p (t - c') = 0 := by
    intro c' hc'
    obtain ⟨hne, hc'C⟩ := Finset.mem_erase.mp hc'
    have hne0 : t - c' ≠ 0 := sub_ne_zero.mpr fun h => ht (h ▸ hc'C)
    refine ⟨hne0, ?_⟩
    obtain ⟨a, rfl, ha1, ha2, -⟩ := contactSet_int hc
    obtain ⟨a', rfl, ha1', ha2', -⟩ := contactSet_int hc'C
    have haa : a - a' ≠ 0 := by
      intro h0; apply hne; rw [show a' = a by omega]
    have hd0 : ((a - a' : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr haa
    have hd : padicValRat p ((a - a' : ℤ) : ℚ) = 0 :=
      padicValRat_intCast_eq_zero haa (by omega)
    have hsum : t - a' = (t - a) + ((a - a' : ℤ) : ℚ) := by push_cast; ring
    rw [hsum, padicValRat.add_eq_min (by rw [← hsum]; exact hne0) htc0 hd0 (by rw [hd]; omega), hd]
    exact min_eq_right hpos.le
  have hprod : (∏ c' ∈ contactSet.erase c, (t - c')) ≠ 0 ∧
      padicValRat p (∏ c' ∈ contactSet.erase c, (t - c')) = 0 :=
    Finset.prod_induction _ (fun x => x ≠ 0 ∧ padicValRat p x = 0)
      (fun x y hx hy => ⟨mul_ne_zero hx.1 hy.1, by rw [padicValRat.mul hx.1 hy.1, hx.2, hy.2,
        add_zero]⟩)
      ⟨one_ne_zero, padicValRat.one⟩ hunit
  rw [padicValRat.mul htc0 hprod.1, hprod.2, add_zero]

/-! ### The valuation of `R` -/

theorem not_dvd_2730 {p : ℕ} (hp : p.Prime) (h13 : 13 < p) : ¬ p ∣ 2730 := by
  intro h
  rw [show (2730 : ℕ) = 2 * (3 * (5 * (7 * 13))) by norm_num] at h
  have key : ∀ q : ℕ, 0 < q → q ≤ 13 → p ∣ q → False := fun q hq hq13 hd => by
    have := Nat.le_of_dvd hq hd; omega
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact key 2 (by norm_num) (by norm_num) h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact key 3 (by norm_num) (by norm_num) h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact key 5 (by norm_num) (by norm_num) h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact key 7 (by norm_num) (by norm_num) h
  · exact key 13 (by norm_num) le_rfl h

/-- `R ≠ 0` and `v_p(R) = v_p(F(t)) + 2b` with `b = v_p(a₀) ≤ 0`, for `p > 13` and `v_p(F(t))`
odd. -/
theorem testR_val {p : ℕ} [hp : Fact p.Prime] (h13 : 13 < p) {η q t : ℚ} (hη : η ^ 2 = 1)
    (hF : contactPoly t ≠ 0) (hodd : Odd (padicValRat p (contactPoly t)))
    (ha0 : 1 - testR₀ η t * q ^ 2 ≠ 0) :
    testR η q t ≠ 0 ∧ ∃ b : ℤ, b ≤ 0 ∧
      padicValRat p (testR η q t) = padicValRat p (contactPoly t) + 2 * b := by
  have hη0 : η ≠ 0 := by rintro rfl; norm_num at hη
  have hηv : padicValRat p η = 0 := by
    have : (η - 1) * (η + 1) = 0 := by linear_combination hη
    rcases mul_eq_zero.mp this with h | h
    · rw [show η = 1 by linarith, padicValRat.one]
    · rw [show η = -1 by linarith, padicValRat.neg, padicValRat.one]
  have h2730 : padicValRat p ((2730 : ℚ) ^ 6) = 0 := by
    rw [padicValRat.pow, show (2730 : ℚ) = ((2730 : ℕ) : ℚ) by norm_num,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (not_dvd_2730 hp.out h13)]
    simp
  have hR₀0 : testR₀ η t ≠ 0 := by unfold testR₀; positivity
  have hR₀v : padicValRat p (testR₀ η t) = padicValRat p (contactPoly t) := by
    unfold testR₀
    rw [padicValRat.mul (by positivity) hF, padicValRat.mul hη0 (by positivity), hηv, h2730]
    ring
  have hb : padicValRat p (1 - testR₀ η t * q ^ 2) ≤ 0 := by
    by_cases hq : q = 0
    · rw [hq]; simp
    have hX : testR₀ η t * q ^ 2 ≠ 0 := by positivity
    have hXv : padicValRat p (testR₀ η t * q ^ 2) = padicValRat p (contactPoly t) +
        2 * padicValRat p q := by
      rw [padicValRat.mul hR₀0 (by positivity), padicValRat.pow, hR₀v]; push_cast; ring
    rw [sub_eq_add_neg, padicValRat.add_eq_min (by rwa [← sub_eq_add_neg]) one_ne_zero
      (neg_ne_zero.mpr hX) (by
        rw [padicValRat.neg, padicValRat.one, hXv]; obtain ⟨m, hm⟩ := hodd; omega),
      padicValRat.one]
    exact min_le_left _ _
  refine ⟨by unfold testR; positivity, _, hb, ?_⟩
  unfold testR
  rw [padicValRat.mul hR₀0 (by positivity), padicValRat.pow, hR₀v]
  push_cast; ring

/-! ### The six tests are small at one prime above `p` -/

section Small

variable {p : ℕ} [Fact p.Prime] {π : Zs}

/-- The valuation of one factor `1 + R Cⱼ²` of `W`, `Cⱼ = Dⱼ / F`, when `v_p(R)` is odd. -/
theorem vp_poleW_factor (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {R F : ℚ}
    (hR : R ≠ 0) (hF : F ≠ 0) (hodd : Odd (padicValRat p R)) (D : K0) :
    vp π (1 + (R : K0) * (D / F) ^ 2) ≤ 0 ∧ (D ≠ 0 →
      vp π (1 + (R : K0) * (D / F) ^ 2) =
        min 0 (padicValRat p R + 2 * (vp π D - padicValRat p F))) := by
  by_cases hD : D = 0
  · rw [hD]; simp [vp_one hπ]
  have hRK : (R : K0) ≠ 0 := Rat.cast_ne_zero.mpr hR
  have hFK : (F : K0) ≠ 0 := Rat.cast_ne_zero.mpr hF
  have hX : (R : K0) * (D / F) ^ 2 ≠ 0 := by positivity
  have hXv : vp π ((R : K0) * (D / F) ^ 2) = padicValRat p R + 2 * (vp π D - padicValRat p F) := by
    rw [vp_mul hπ hRK (by positivity), vp_pow hπ, vp_div hπ hD hFK, Mult.vp_ratCast hp2 hπ hπp,
      Mult.vp_ratCast hp2 hπ hπp]
    push_cast; ring
  have hne : vp π 1 ≠ vp π ((R : K0) * (D / F) ^ 2) := by
    rw [vp_one hπ, hXv]; obtain ⟨m, hm⟩ := hodd; omega
  have heq := vp_add_eq_min_of_ne hπ one_ne_zero hX hne
  rw [vp_one hπ, hXv] at heq
  exact ⟨by rw [heq]; exact min_le_left _ _, fun _ => heq⟩

/-- **The six tests are small.** If `v_p(R)` is odd and `2 v_π(W) > -v_p(R)`, then every
`Dⱼ ≠ 0` has `4 v_π(Dⱼ) > 4 v_p(F) - 3 v_p(R)`. -/
theorem tests_small (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {R F : ℚ} (hR : R ≠ 0)
    (hF : F ≠ 0) (hodd : Odd (padicValRat p R)) (D C : Fin 6 → K0) (hC : ∀ j, C j = D j / F)
    (hW : poleW R C ≠ 0) (hlam : -padicValRat p R < 2 * vp π (poleW R C)) (j : Fin 6) :
    D j = 0 ∨ 4 * padicValRat p F - 3 * padicValRat p R < 4 * vp π (D j) := by
  classical
  have hW' : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 1 + (R : K0) * C i ^ 2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hW
  have hfac := fun i => vp_poleW_factor hp2 hπ hπp hR hF hodd (D i)
  have hsum : vp π (poleW R C) = ∑ i, vp π (1 + (R : K0) * (D i / F) ^ 2) := by
    rw [poleW, vp_prod hπ _ _ hW']; simp only [hC]
  have hle : vp π (poleW R C) ≤ vp π (1 + (R : K0) * (D j / F) ^ 2) := by
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have : ∑ i ∈ Finset.univ.erase j, vp π (1 + (R : K0) * (D i / F) ^ 2) ≤ 0 :=
      Finset.sum_nonpos fun i _ => (hfac i).1
    omega
  by_cases hD : D j = 0
  · exact Or.inl hD
  right
  rw [(hfac j).2 hD] at hle
  have := hle.trans (min_le_right _ _)
  omega

/-- The trace bound: if `v_π(W)` is the larger of `v_π(W)`, `v_{σπ}(W)`, then
`v_p(Tr W⁻¹) ≥ -v_π(W)`. -/
theorem trace_val (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {W : K0}
    (hmax : vp (star π) W ≤ vp π W) (hΘ : QuadraticAlgebra.trace W⁻¹ ≠ 0) :
    -vp π W ≤ padicValRat p (QuadraticAlgebra.trace W⁻¹) := by
  have h1 : -vp π W ≤ vp π W⁻¹ := by rw [vp_inv hπ]
  have h2 : -vp π W ≤ vp (star π) W⁻¹ := by rw [vp_inv (prime_star hπ)]; omega
  exact (Mult.vp_trace_ge hp2 hπ hπp h1 h2).resolve_left hΘ

/-- The pole step: `Φ(R/Θ²)` with `v_p(R)` odd and `p > 13` forces `v_p(R) > 2 v_p(Θ)`. -/
theorem pole_step (h13 : 13 < p) {R Θ : ℚ} (hR : R ≠ 0) (hΘ : Θ ≠ 0)
    (hodd : Odd (padicValRat p R)) (hΦ : PoleSoluble (R / Θ ^ 2)) :
    2 * padicValRat p Θ < padicValRat p R := by
  have hB : R / Θ ^ 2 ≠ 0 := by positivity
  have hv : padicValRat p (R / Θ ^ 2) = padicValRat p R - 2 * padicValRat p Θ := by
    rw [padicValRat.div hR (by positivity), padicValRat.pow]; push_cast; ring
  have := poleSoluble_no_negative_odd hB hΦ (Fact.out : p.Prime)
    (not_dvd_2730 (Fact.out : p.Prime) h13)
  rw [hv] at this
  obtain ⟨m, hm⟩ := hodd
  by_contra hc
  exact this ⟨by omega, ⟨m - padicValRat p Θ, by omega⟩⟩

end Small

/-! ### The formal-group step -/

section Formal

variable {p : ℕ} [Fact p.Prime] {π : Zs}

/-- A multiple of `P₀` with `v_π(w) ≥ 1` lies in `E₁(π)`. -/
theorem mem_Ek_one_of_wCoord (hπ : Prime π) {m : ℤ}
    (hw : Vge (vP π hπ) 1 (wCoord (A := -genD ^ 2) (m • genP0))) : m • genP0 ∈ Ek π hπ 1 := by
  by_cases hm : m = 0
  · rw [hm, zero_zsmul]; exact (Ek π hπ 1).zero_mem
  obtain ⟨x, y, h, hkP, hy⟩ := admissible_of_ne_zero hm
  have hx : x ≠ 0 := x_ne_zero_of_y_ne_zero h.1 hy
  rw [hkP] at hw ⊢
  change Vge (vP π hπ) 1 (1 / x) at hw
  change _ ∈ formalFilt (-genD ^ 2) (vP_genA_nonneg π hπ) 1
  refine (mem_formalNbhd_iff _ _).mpr ?_
  change vP π hπ x < 0
  obtain ⟨k, hk⟩ := val_eq_coe (v := vP π hπ) hx
  rw [one_div, vge_iff_of_eq (val_inv_coe hk)] at hw
  rw [hk]; exact_mod_cast (show k < 0 by omega)

/-- **The congruence from a ratio test.** If `[a]P₀, [b]P₀ ∈ E₁(π)` with `a ≠ 0`, `t` is
`π`-integral and `v_π(z([b]P₀)/z([a]P₀) - t) ≥ 1`, then `v_π(b - t a) ≥ 1`. -/
theorem ratio_congr (hp2 : p ≠ 2) (hπ : Prime π) (hπp : π ∣ (p : Zs)) {a b : ℤ} (ha : a ≠ 0)
    (hA : a • genP0 ∈ Ek π hπ 1) (hB : b • genP0 ∈ Ek π hπ 1) {t : ℚ}
    (ht : Vge (vP π hπ) 0 (t : K0))
    (hD : Vge (vP π hπ) 1 (Mult.zCoord (A := -genD ^ 2) (b • genP0) /
      Mult.zCoord (A := -genD ^ 2) (a • genP0) - t)) :
    Vge (vP π hπ) 1 ((b - t * a : ℚ) : K0) := by
  set g : ℤ := (Int.gcd a b : ℤ) with hg
  have hg0 : g ≠ 0 := by have := Int.gcd_pos_of_ne_zero_left b ha; omega
  obtain ⟨a', ha'⟩ : g ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Int.gcd_dvd_right a b
  have ha'0 : a' ≠ 0 := by rintro rfl; rw [mul_zero] at ha'; exact ha ha'
  have hQ : g • genP0 ∈ Ek π hπ 1 := by
    have : g • genP0 = Int.gcdA a b • (a • genP0) + Int.gcdB a b • (b • genP0) := by
      rw [smul_smul, smul_smul, ← add_zsmul, hg, Int.gcd_eq_gcd_ab]; congr 1; ring
    rw [this]; exact add_mem (zsmul_mem hA _) (zsmul_mem hB _)
  have hQ0 : g • genP0 ≠ 0 := zsmul_genP0_ne_zero hg0
  have haQ : a • genP0 = a' • (g • genP0) := by rw [smul_smul, ha', mul_comm]
  have hbQ : b • genP0 = b' • (g • genP0) := by rw [smul_smul, hb', mul_comm]
  obtain ⟨w, hw, hw0, hw1⟩ := zCoord_zsmul_ratio_K0 hp2 hπ hπp hQ hQ0 ha'0 (b := b')
  rw [haQ, hbQ, hw] at hD
  have hw0' : w ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hw0; exact WithTop.top_ne_coe hw0
  have haK : (a : K0) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hgK : (g : K0) ≠ 0 := Int.cast_ne_zero.mpr hg0
  have ha'K : (a' : K0) ≠ 0 := Int.cast_ne_zero.mpr ha'0
  set r : ℚ := (b : ℚ) / a with hr
  have hrK : (b' : K0) / a' = (r : K0) := by
    rw [hr, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, ha', hb']; push_cast
    field_simp
  rw [hrK] at hD
  have hr0 : Vge (vP π hπ) 0 (r : K0) := by
    have : (r : K0) = ((r : K0) * w - t + t) / w := by field_simp; ring
    rw [this]; exact ((hD.mono (by norm_num)).add ht).div_unit hw0
  have hrt : Vge (vP π hπ) 1 ((r : K0) - t) := by
    have : (r : K0) - t = ((r : K0) * w - t) - r * (w - 1) := by ring
    rw [this]; exact hD.sub ((hr0.mul hw1).mono (by norm_num))
  have : ((b - t * a : ℚ) : K0) = (a : K0) * ((r : K0) - t) := by
    rw [hr]; push_cast; field_simp
  rw [this]
  exact ((Mult.vge_intCast a).mul hrt).mono (by norm_num)

end Formal

/-! ### Divisibility -/

/-- **The local step of Lemma 11.1.** If `Test(n, κ, t)` holds and `p > 324` is a prime with
`v_p(t - c)` positive and odd for a contact value `c`, then `p ∣ κ F(n)`. -/
theorem prime_dvd_of_test {n κ : ℤ} {t : ℚ} (hT : Test n κ t) {p : ℕ} [Fact p.Prime]
    (hp : 324 < p) {c : ℚ} (hc : c ∈ contactSet) (hpos : 0 < padicValRat p (t - c))
    (hodd : Odd (padicValRat p (t - c))) : (p : ℤ) ∣ κ * sixF n := by
  obtain ⟨hκ, htC, h, s₀, η, q, hh, hhκ, hη, ha0, hW, hΘ, hΦ⟩ := hT
  have hp2 : p ≠ 2 := by omega
  have hF : contactPoly t ≠ 0 := contactPoly_ne_zero_iff.mpr htC
  have hFv := contact_val (by omega) hc htC hpos
  obtain ⟨hR, b, hb, hRv⟩ := testR_val (by omega) hη hF (hFv ▸ hodd) ha0
  have hRodd : Odd (padicValRat p (testR η q t)) := by
    obtain ⟨m, hm⟩ := hodd; exact ⟨m + b, by rw [hRv, hFv, hm]; ring⟩
  have hB := pole_step (by omega) hR hΘ hRodd hΦ
  obtain ⟨a, rfl, -, -, hdvd⟩ := contactSet_int hc
  set W := poleW (testR η q t) (testC n κ t h s₀) with hWdef
  -- the argument at a prime `π₀ ∣ p` where `v_π(W)` is maximal
  have key : ∀ (π₀ : Zs) (hπ₀ : Prime π₀), π₀ ∣ (p : Zs) → vp (star π₀) W ≤ vp π₀ W →
      (p : ℤ) ∣ κ * sixF n := by
    intro π₀ hπ₀ hπ₀p hmax
    have hπ₁p := star_dvd_natCast hπ₀p
    have htr := trace_val hp2 hπ₀ hπ₀p hmax hΘ
    have hlam : -padicValRat p (testR η q t) < 2 * vp π₀ W := by
      change 2 * padicValRat p (QuadraticAlgebra.trace W⁻¹) < _ at hB; omega
    have hsmall : ∀ j, Vge (vP π₀ hπ₀) 1 (testD n κ t h s₀ j) := by
      intro j
      rcases tests_small hp2 hπ₀ hπ₀p hR hF hRodd (testD n κ t h s₀) (testC n κ t h s₀)
        (fun _ => rfl) hW hlam j with h0 | hlt
      · rw [h0]; exact Vge.zero _
      · rw [Vge, le_vP_iff]; right; rw [hFv, hRv] at hlt; omega
    have hD1 := hsmall 0
    have hD2 := hsmall 1
    have hD3 := hsmall 2
    have hD4 := hsmall 3
    have hD5 := hsmall 4
    have hD6 := hsmall 5
    simp only [testD] at hD1 hD2 hD3 hD4 hD5 hD6
    change Vge _ 1 (wCoord (A := -genD ^ 2) (h • genP0)) at hD1
    change Vge _ 1 (wCoord (A := -genD ^ 2) (s₀ • genP0)) at hD2
    change Vge _ 1 (star (wCoord (A := -genD ^ 2) ((h - κ) • genP0))) at hD3
    change Vge _ 1 (star (wCoord (A := -genD ^ 2) ((s₀ - κ * n) • genP0))) at hD4
    change Vge _ 1 (Mult.zCoord (A := -genD ^ 2) (s₀ • genP0) /
      Mult.zCoord (A := -genD ^ 2) (h • genP0) - t) at hD5
    change Vge _ 1 (star (Mult.zCoord (A := -genD ^ 2) ((s₀ - κ * n) • genP0) /
      Mult.zCoord (A := -genD ^ 2) ((h - κ) • genP0)) - t) at hD6
    have hHm := mem_Ek_one_of_wCoord hπ₀ hD1
    have hUm := mem_Ek_one_of_wCoord hπ₀ hD2
    have hV₀m := mem_Ek_one_of_wCoord (prime_star hπ₀) ((vge_star_iff hπ₀ 1 _).mpr hD3)
    have hV₁m := mem_Ek_one_of_wCoord (prime_star hπ₀) ((vge_star_iff hπ₀ 1 _).mpr hD4)
    have htc : Vge (vP π₀ hπ₀) 1 ((t - a : ℚ) : K0) :=
      (vge_ratCast_iff hp2 hπ₀ hπ₀p 1 _).mpr (Or.inr (by omega))
    have htint : Vge (vP π₀ hπ₀) 0 (t : K0) := by
      have : (t : K0) = ((t - a : ℚ) : K0) + ((a : ℤ) : K0) := by push_cast; ring
      rw [this]; exact (htc.mono (by norm_num)).add (Mult.vge_intCast a)
    have h1 := ratio_congr hp2 hπ₀ hπ₀p hh hHm hUm htint hD5
    have h2 := ratio_congr hp2 (prime_star hπ₀) hπ₁p (sub_ne_zero.mpr hhκ) hV₀m hV₁m
      ((vge_star_ratCast_iff hπ₀ 0 t).mpr htint)
      ((vge_star_iff hπ₀ 1 _).mpr (by rwa [star_sub, star_ratCast]))
    rw [vge_star_ratCast_iff hπ₀] at h2
    have hfin := (h1.sub h2).add (((Mult.vge_intCast κ).mul htc).mono (by norm_num))
    have hid : ((κ * (n - a) : ℤ) : K0) = ((s₀ - t * h : ℚ) : K0) -
        ((((s₀ - κ * n : ℤ) : ℚ) - t * ((h - κ : ℤ) : ℚ) : ℚ) : K0) +
        (κ : K0) * ((t - a : ℚ) : K0) := by
      push_cast; ring
    have := dvd_of_vge_intCast hp2 hπ₀ hπ₀p (by rw [hid]; exact hfin)
    exact this.trans (mul_dvd_mul_left κ (hdvd n))
  obtain ⟨π, hπ, hπp⟩ := exists_prime_dvd_natCast p
  rcases le_total (vp (star π) W) (vp π W) with hle | hle
  · exact key π hπ hπp hle
  · exact key (star π) (prime_star hπ) (star_dvd_natCast hπp) (by rwa [star_star])

/-- **Divisibility from the six local tests** (Lemma 11.1). If `Test(n, κ, t)` holds, then
`M_{S_ht}(t) ∣ κ F(n)`. -/
theorem test_dvd {n κ : ℤ} {t : ℚ} (hT : Test n κ t) :
    contactSupport heightPrimes t ∣ (κ * sixF n).natAbs := by
  classical
  unfold contactSupport
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpf, hpS, c, hc, hpos, hodd⟩ := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpf
    have := Fact.mk hpp
    have h324 : 324 < p := by
      by_contra hle; exact hpS (mem_heightPrimes.mpr ⟨hpp, by omega⟩)
    exact Int.natCast_dvd.mp (prime_dvd_of_test hT h324 hc hpos hodd)

end ZInQ.Assembly
