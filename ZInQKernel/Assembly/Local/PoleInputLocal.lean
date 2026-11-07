import ZInQKernel.Assembly.Local.DeepMultiples
import ZInQKernel.Assembly.Local.DyadicTrace
import ZInQKernel.Assembly.Local.TestDivisibility

/-!
# Local conditions on the pole input

Blueprint: `assembly/local-tests/pole-input-local.md`.

Let `n ∉ 𝒞`, `η² = 1`, `R₀ = η · 2730⁶ · F(n)`, and `κ ≥ 1` such that for every prime `π` of
`ℤ[s]` dividing `Z = 2730⁶ F(n)` there is `N ≥ max(1, v_π(F(n)))` with `[κ]P₀ ∈ E_N(π)`. Take
`h = 2κ`, `s₀ = 2κn` and the six tests at `t = n`. If `v_p(q) ≥ 0` for every prime `p ∣ Z`
and `a₀, W, Θ ≠ 0`, then `B = R/Θ²` has `v₂(B) ≥ 4`, `v_p(B) ≥ 6` for `p = 3, 5, 7, 13`, and a
square reduced denominator (`poleInput_local`).

* At every `π ∣ Z` the six tests have `v_π(Dⱼ) ≥ v_π(F(n))` (`tests_deep`), so
  `v_π(W⁻¹ - 1) ≥ v_π(Z)` (`inv_poleW_close`).
* The trace bounds give `v_p(Θ) = 0` for odd `p ∣ Z` and `v₂(Θ) = 1` (`val_theta_odd`,
  `val_theta_two`); `v_p(R) = v_p(Z)` for `p ∣ Z` and `v_p(R)` is even otherwise.

The article takes `η` with the sign of `F(n)` (so that `R₀ > 0`); the local conditions hold for
both signs.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult ZInQ.Compiler.Precision

/-- The pole input `B = R/Θ²` of the six local tests. -/
noncomputable def testB (n κ : ℤ) (t η q : ℚ) (h s₀ : ℤ) : ℚ :=
  testR η q t / poleTheta (testR η q t) (testC n κ t h s₀) ^ 2

/-! ### Reduced denominators -/

/-- `v_p(den B) = max(0, -v_p(B))`. -/
theorem den_val (B : ℚ) (p : ℕ) [hp : Fact p.Prime] :
    (padicValNat p B.den : ℤ) = max 0 (-padicValRat p B) := by
  rw [padicValRat_def]
  by_cases hd : p ∣ B.den
  · have hn : ¬ (p : ℤ) ∣ B.num := by
      intro hn
      have h1 : Nat.Coprime p B.den := Nat.Coprime.coprime_dvd_left (Int.natCast_dvd.mp hn) B.reduced
      exact hp.out.one_lt.ne' (h1.eq_one_of_dvd hd)
    rw [padicValInt.eq_zero_of_not_dvd hn]
    simp only [Nat.cast_zero, zero_sub, neg_neg]
    exact (max_eq_right (Nat.cast_nonneg _)).symm
  · rw [padicValNat.eq_zero_of_not_dvd hd]
    simp only [Nat.cast_zero, sub_zero]
    exact (max_eq_left (neg_nonpos.mpr (Nat.cast_nonneg _))).symm

/-- A rational number whose negative valuations are all even has a square reduced
denominator. -/
theorem isSquare_den_of (B : ℚ)
    (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p B ∨ Even (padicValRat p B)) : IsSquare B.den := by
  rw [Nat.isSquare_iff_even_factorization]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp]
  have hv := den_val B p
  rcases h p hp with h0 | ⟨m, hm⟩
  · rw [show padicValNat p B.den = 0 by omega]; exact ⟨0, rfl⟩
  · rcases le_total 0 (padicValRat p B) with h0 | h0
    · rw [show padicValNat p B.den = 0 by omega]; exact ⟨0, rfl⟩
    · exact ⟨(-m).toNat, by omega⟩

/-! ### Primes of `ℤ[s]` dividing an integer -/

theorem not_dvd_natCast_of_coprime {π : Zs} (hπ : Prime π) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : π ∣ (a : Zs)) : ¬ π ∣ (b : Zs) := by
  intro hb
  have hcop : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  have hcop' : IsCoprime (a : Zs) (b : Zs) := by simpa using hcop.map (Int.castRingHom Zs)
  exact hπ.not_isUnit (hcop'.isUnit_of_dvd' ha hb)

theorem dvd_intCast_iff_natAbs {π : Zs} {Z : ℤ} : π ∣ (Z : Zs) ↔ π ∣ (Z.natAbs : Zs) := by
  rcases Int.natAbs_eq Z with h | h
  · rw [show (Z : Zs) = ((Z.natAbs : ℤ) : Zs) by rw [← h], Int.cast_natCast]
  · rw [show (Z : Zs) = -((Z.natAbs : ℤ) : Zs) by rw [← Int.cast_neg, ← h], Int.cast_natCast,
      dvd_neg]

/-- The rational prime below a prime `π ∣ Z` divides `Z`. -/
theorem natCast_dvd_of_dvd {π : Zs} (hπ : Prime π) {Z : ℤ} (hπZ : π ∣ (Z : Zs)) {p : ℕ}
    (hp : p.Prime) (hπp : π ∣ (p : Zs)) : (p : ℤ) ∣ Z := by
  rcases Nat.coprime_or_dvd_of_prime hp Z.natAbs with hc | hd
  · exact absurd (dvd_intCast_iff_natAbs.mp hπZ) (not_dvd_natCast_of_coprime hπ hc hπp)
  · exact Int.natCast_dvd.mpr hd

/-- A rational with `v_p(q) ≥ 0` is integral at every prime `π ∣ p`. -/
theorem vge_zero_ratCast {π : Zs} (hπ : Prime π) {p : ℕ} [hp : Fact p.Prime]
    (hπp : π ∣ (p : Zs)) {q : ℚ} (hq : 0 ≤ padicValRat p q) : Vge (vP π hπ) 0 (q : K0) := by
  have hd : ¬ p ∣ q.den := by
    intro hd
    have := den_val q p
    have h1 := one_le_padicValNat_of_dvd q.den_nz hd
    omega
  have hq' : (q : K0) = (q.num : K0) / (q.den : K0) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden0 : (q.den : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this
  have hden : vP π hπ (q.den : K0) = ((0 : ℤ) : WithTop ℤ) := by
    rw [vP_apply hπ (Nat.cast_ne_zero.mpr q.den_nz), ← toK0_natCast,
      (vp_eq_zero_iff hπ hden0).mpr (not_dvd_natCast_of_coprime hπ
        ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd) hπp)]
  rw [hq']
  exact ((Mult.vge_intCast q.num).div_val' hden).mono (by simp)

/-! ### Products and points -/

theorem vp_nonneg_intCast {π : Zs} (hπ : Prime π) (m : ℤ) : 0 ≤ vp π (m : K0) := by
  rw [← toK0_intCast]; exact vp_nonneg hπ _

theorem vge_prod_sub_one {v : AddValuation K0 (WithTop ℤ)} {e : ℤ} (he : 0 ≤ e) {X : Fin 6 → K0}
    (hX : ∀ j, Vge v e (X j)) : Vge v e (∏ j, (1 + X j) - 1) :=
  Finset.prod_induction (fun j => 1 + X j) (fun y => Vge v e (y - 1))
    (fun a b ha hb => by
      have : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
      rw [this]; exact (ha.add hb).add ((ha.mul hb).mono (by omega)))
    (by rw [sub_self]; exact Vge.zero _)
    (fun j _ => by rw [add_sub_cancel_left]; exact hX j)

theorem vge_wCoord_of_mem {π : Zs} (hπ : Prime π) {N : ℤ} {P : genCurve.toAffine.Point}
    (hP : P ∈ Ek π hπ N) : Vge (vP π hπ) (2 * N) (wCoord (A := -genD ^ 2) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact Vge.zero _
  obtain ⟨N₀, -, -, -, -, hz, hw, -⟩ := formal_val_x_y (vP_genA_nonneg π hπ) h hP.1
  have hN : N ≤ N₀ := by have := hP.2.trans_eq hz; exact_mod_cast this
  exact (Vge.of_eq hw).mono (by omega)

theorem vge_zCoord_ratio_of_mem {π : Zs} (hπ : Prime π) {N : ℤ} {P : genCurve.toAffine.Point}
    (hP : P ∈ Ek π hπ N) (hP0 : P ≠ 0) (m : ℤ) :
    Vge (vP π hπ) (4 * N) (Mult.zCoord (A := -genD ^ 2) (m • P) /
      Mult.zCoord (A := -genD ^ 2) P - m) := by
  obtain ⟨k, -, hk⟩ := val_zCoord_of_mem_W1 (vP_genA_nonneg π hπ) hP.1 hP0
  have hNk : N ≤ k := by have := hP.2.trans_eq hk; exact_mod_cast this
  exact ((val_zCoord_zsmul_sub (vP_genA_nonneg π hπ) hP.1 hk m).2).mono (by omega)

/-- **The six tests are divisible by `F(n)` at a deep prime.** -/
theorem tests_deep {n κ : ℤ} (hκ : κ ≠ 0) {π : Zs} (hπ : Prime π) {N N' : ℤ}
    (hF : vp π (sixF n : K0) ≤ N) (hF' : vp π (sixF n : K0) ≤ N')
    (hmem : κ • genP0 ∈ Ek π hπ N) (hmem' : κ • genP0 ∈ Ek (star π) (prime_star hπ) N')
    (j : Fin 6) :
    Vge (vP π hπ) (vp π (sixF n : K0)) (testD n κ n (2 * κ) (2 * κ * n) j) := by
  have hQ0 : κ • genP0 ≠ 0 := zsmul_genP0_ne_zero hκ
  have hH0 : (2 : ℤ) • (κ • genP0) ≠ 0 := by
    rw [smul_smul]; exact zsmul_genP0_ne_zero (by omega)
  have e1 : (2 * κ) • genP0 = (2 : ℤ) • (κ • genP0) := by rw [smul_smul]
  have e2 : (2 * κ * n) • genP0 = n • ((2 : ℤ) • (κ • genP0)) := by
    rw [smul_smul, smul_smul]; congr 1; ring
  have e3 : (2 * κ - κ) • genP0 = κ • genP0 := by congr 1; ring
  have e4 : (2 * κ * n - κ * n) • genP0 = n • (κ • genP0) := by rw [smul_smul]; congr 1; ring
  have hH : (2 : ℤ) • (κ • genP0) ∈ Ek π hπ N := zsmul_mem hmem 2
  fin_cases j
  · show Vge _ _ (wCoord (A := -genD ^ 2) ((2 * κ) • genP0))
    rw [e1]; exact (vge_wCoord_of_mem hπ hH).mono (by
      have := le_trans (vp_nonneg_intCast hπ (sixF n)) hF; omega)
  · show Vge _ _ (wCoord (A := -genD ^ 2) ((2 * κ * n) • genP0))
    rw [e2]; exact (vge_wCoord_of_mem hπ (zsmul_mem hH n)).mono (by
      have := le_trans (vp_nonneg_intCast hπ (sixF n)) hF; omega)
  · show Vge _ _ (star (wCoord (A := -genD ^ 2) ((2 * κ - κ) • genP0)))
    rw [e3, ← vge_star_iff]; exact (vge_wCoord_of_mem _ hmem').mono (by
      have := le_trans (vp_nonneg_intCast hπ (sixF n)) hF'; omega)
  · show Vge _ _ (star (wCoord (A := -genD ^ 2) ((2 * κ * n - κ * n) • genP0)))
    rw [e4, ← vge_star_iff]; exact (vge_wCoord_of_mem _ (zsmul_mem hmem' n)).mono (by
      have := le_trans (vp_nonneg_intCast hπ (sixF n)) hF'; omega)
  · show Vge _ _ (Mult.zCoord (A := -genD ^ 2) ((2 * κ * n) • genP0) /
      Mult.zCoord (A := -genD ^ 2) ((2 * κ) • genP0) - ((n : ℚ) : K0))
    rw [e1, e2, Rat.cast_intCast]
    exact (vge_zCoord_ratio_of_mem hπ hH hH0 n).mono (by
      have := le_trans (vp_nonneg_intCast hπ (sixF n)) hF; omega)
  · show Vge _ _ (star (Mult.zCoord (A := -genD ^ 2) ((2 * κ * n - κ * n) • genP0) /
      Mult.zCoord (A := -genD ^ 2) ((2 * κ - κ) • genP0)) - ((n : ℚ) : K0))
    rw [e3, e4, Rat.cast_intCast, ← star_intCast (R := K0) n, ← star_sub, ← vge_star_iff]
    exact (vge_zCoord_ratio_of_mem _ hmem' hQ0 n).mono (by
      have := le_trans (vp_nonneg_intCast hπ (sixF n)) hF'; omega)

/-! ### `W ≡ 1` at the primes of `Z` -/

theorem padicValRat_of_sq_eq_one {η : ℚ} (hη : η ^ 2 = 1) (p : ℕ) : padicValRat p η = 0 := by
  have : (η - 1) * (η + 1) = 0 := by linear_combination hη
  rcases mul_eq_zero.mp this with h | h
  · rw [show η = 1 by linarith, padicValRat.one]
  · rw [show η = -1 by linarith, padicValRat.neg, padicValRat.one]

theorem vP_of_sq_eq_one {π : Zs} (hπ : Prime π) {η : ℚ} (hη : η ^ 2 = 1) :
    vP π hπ (η : K0) = ((0 : ℤ) : WithTop ℤ) := by
  have : (η - 1) * (η + 1) = 0 := by linear_combination hη
  rcases mul_eq_zero.mp this with h | h
  · rw [show η = 1 by linarith, Rat.cast_one, AddValuation.map_one]; rfl
  · rw [show η = -1 by linarith, Rat.cast_neg, Rat.cast_one, AddValuation.map_neg,
      AddValuation.map_one]; rfl

theorem star_dvd_intCast {π : Zs} {Z : ℤ} (h : π ∣ (Z : Zs)) : star π ∣ (Z : Zs) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨star c, ?_⟩
  have := congrArg star hc
  rw [star_intCast, star_mul] at this
  rw [this, mul_comm]

/-- At a prime `π ∣ Z` at which `q` and the `Cⱼ` are integral, `W` is a unit and
`v_π(W⁻¹ - 1) ≥ v_π(Z)`, for `R₀ = η Z` and `R = R₀ (1 - R₀ q²)²`. -/
theorem inv_poleW_close {π : Zs} (hπ : Prime π) {Z : ℤ} (hZ : Z ≠ 0) (hπZ : π ∣ (Z : Zs))
    {η q : ℚ} (hη : η ^ 2 = 1) {R₀ : ℚ} (hR₀ : R₀ = η * Z) (hq : Vge (vP π hπ) 0 (q : K0))
    {C : Fin 6 → K0} (hC : ∀ j, Vge (vP π hπ) 0 (C j)) :
    Vge (vP π hπ) (vp π (Z : K0)) ((poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C)⁻¹ - 1) := by
  set vZ := vp π (Z : K0) with hvZ
  have hZK : (Z : K0) ≠ 0 := Int.cast_ne_zero.mpr hZ
  have hvZ1 : 1 ≤ vZ := by
    have hZs : (Z : Zs) ≠ 0 := by
      intro h; have := congrArg QuadraticAlgebra.re h; simp at this; exact hZ this
    have := (vp_pos_iff hπ hZs).mpr hπZ
    rw [toK0_intCast] at this; omega
  have hZv : vP π hπ (Z : K0) = (vZ : WithTop ℤ) := vP_apply hπ hZK
  have hR₀v : Vge (vP π hπ) vZ (R₀ : K0) := by
    rw [hR₀, Rat.cast_mul, Rat.cast_intCast]
    exact ((Vge.of_eq (vP_of_sq_eq_one hπ hη)).mul (Vge.of_eq hZv)).mono (by omega)
  have hX : Vge (vP π hπ) vZ ((R₀ : K0) * (q : K0) ^ 2) :=
    (hR₀v.mul (hq.pow 2)).mono (by omega)
  have ha0 : Vge (vP π hπ) 0 (1 - (R₀ : K0) * (q : K0) ^ 2) :=
    (show Vge (vP π hπ) 0 (1 : K0) by simpa using Mult.vge_natCast (v := vP π hπ) 1).sub
      (hX.mono (by omega))
  have hR : Vge (vP π hπ) vZ (((R₀ * (1 - R₀ * q ^ 2) ^ 2 : ℚ)) : K0) := by
    push_cast; exact (hR₀v.mul (ha0.pow 2)).mono (by omega)
  have hW1 : Vge (vP π hπ) vZ (poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C - 1) :=
    vge_prod_sub_one (by omega) fun j => (hR.mul ((hC j).pow 2)).mono (by omega)
  have hWv : vP π hπ (poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C) = 0 := by
    have := val_one_add (hW1.mono hvZ1); rwa [add_sub_cancel] at this
  have hW0 : poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hWv; exact WithTop.top_ne_coe hWv
  have : (poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C)⁻¹ - 1 =
      -(poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C - 1) / poleW (R₀ * (1 - R₀ * q ^ 2) ^ 2) C := by
    field_simp; ring
  rw [this]
  exact hW1.neg.div_unit hWv

theorem padicValRat_2730 {p : ℕ} (hp : p ∈ ({2, 3, 5, 7, 13} : Finset ℕ)) :
    padicValRat p 2730 = 1 := by
  have key : ∀ m : ℕ, p.Prime → ¬ p ∣ m → p * m = 2730 → padicValRat p 2730 = 1 := by
    intro m hpp hm hpm
    have := Fact.mk hpp
    have hm0 : m ≠ 0 := by rintro rfl; simp at hpm
    rw [show (2730 : ℚ) = (p : ℚ) * (m : ℚ) by exact_mod_cast hpm.symm,
      padicValRat.mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast hm0),
      padicValRat.self hpp.one_lt, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hm]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact key 1365 (by norm_num) (by decide) (by norm_num)
  · exact key 910 (by norm_num) (by decide) (by norm_num)
  · exact key 546 (by norm_num) (by decide) (by norm_num)
  · exact key 390 (by norm_num) (by decide) (by norm_num)
  · exact key 210 (by norm_num) (by decide) (by norm_num)

/-- **Local conditions on the pole input.** -/
theorem poleInput_local {n : ℤ} (hn : (n : ℚ) ∉ contactSet) {η : ℚ} (hη : η ^ 2 = 1) {κ : ℤ}
    (hκ : 1 ≤ κ)
    (hdeep : ∀ (π : Zs) (hπ : Prime π), π ∣ ((2730 ^ 6 * sixF n : ℤ) : Zs) →
      ∃ N : ℤ, 1 ≤ N ∧ vp π (sixF n : K0) ≤ N ∧ κ • genP0 ∈ Ek π hπ N)
    {q : ℚ} (hq : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2730 ^ 6 * sixF n → 0 ≤ padicValRat p q)
    (ha0 : 1 - testR₀ η n * q ^ 2 ≠ 0)
    (hW : poleW (testR η q n) (testC n κ n (2 * κ) (2 * κ * n)) ≠ 0)
    (hΘ : poleTheta (testR η q n) (testC n κ n (2 * κ) (2 * κ * n)) ≠ 0) :
    4 ≤ padicValRat 2 (testB n κ n η q (2 * κ) (2 * κ * n)) ∧
      (∀ p ∈ ({3, 5, 7, 13} : Finset ℕ),
        6 ≤ padicValRat p (testB n κ n η q (2 * κ) (2 * κ * n))) ∧
      IsSquare (testB n κ n η q (2 * κ) (2 * κ * n)).den := by
  set F := sixF n with hFdef
  have hF0 : F ≠ 0 := by
    have := contactPoly_ne_zero_iff.mpr hn
    rw [contactPoly_intCast] at this; exact_mod_cast this
  set Z : ℤ := 2730 ^ 6 * F with hZdef
  have hZ0 : Z ≠ 0 := mul_ne_zero (by norm_num) hF0
  have hZK : ((Z : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hZ0
  set C := testC n κ n (2 * κ) (2 * κ * n) with hCdef
  have hR₀ : testR₀ η n = η * Z := by
    rw [testR₀, contactPoly_intCast, hZdef]; push_cast; ring
  have hη0 : η ≠ 0 := by rintro rfl; norm_num at hη
  have hR₀0 : testR₀ η n ≠ 0 := by rw [hR₀]; exact mul_ne_zero hη0 hZK
  have hRdef : testR η q n = testR₀ η n * (1 - testR₀ η n * q ^ 2) ^ 2 := rfl
  have hR0 : testR η q n ≠ 0 := by rw [hRdef]; exact mul_ne_zero hR₀0 (pow_ne_zero 2 ha0)
  set R := testR η q n with hRR
  set Θ := poleTheta R C with hΘdef
  -- `W⁻¹ ≡ 1` at every prime `π ∣ Z`
  have hlocal : ∀ (π : Zs) (hπ : Prime π), π ∣ (Z : Zs) →
      Vge (vP π hπ) (vp π (Z : K0)) ((poleW R C)⁻¹ - 1) := by
    intro π hπ hπZ
    obtain ⟨N, hN, hFN, hmem⟩ := hdeep π hπ hπZ
    obtain ⟨N', hN', hFN', hmem'⟩ := hdeep (star π) (prime_star hπ) (star_dvd_intCast hπZ)
    have hFσ : vp (star π) (F : K0) = vp π (F : K0) := by rw [Mult.vp_star hπ, star_intCast]
    rw [hFσ] at hFN'
    have hD := tests_deep (by omega) hπ hFN hFN' hmem hmem'
    have hC : ∀ j, Vge (vP π hπ) 0 (C j) := by
      intro j
      have hFv : vP π hπ ((contactPoly n : ℚ) : K0) = ((vp π (F : K0) : ℤ) : WithTop ℤ) := by
        rw [contactPoly_intCast, Rat.cast_intCast, vP_apply hπ (Int.cast_ne_zero.mpr hF0)]
      have := (hD j).div_val' hFv
      rw [sub_self] at this; exact this
    obtain ⟨p, hp, hπp⟩ := exists_prime_below hπ
    have := Fact.mk hp
    have hqπ := vge_zero_ratCast hπ hπp (hq p hp (natCast_dvd_of_dvd hπ hπZ hp hπp))
    exact inv_poleW_close hπ hZ0 hπZ hη hR₀ hqπ hC
  have htr : QuadraticAlgebra.trace ((poleW R C)⁻¹ - 1) = Θ - 2 := by
    rw [K0.trace_eq, hΘdef, poleTheta, K0.trace_eq, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.re_one]; ring
  have hpZ1 : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ Z → 1 ≤ (padicValInt p Z : ℤ) := by
    intro p hp hpZ
    have := Fact.mk hp
    have := (padicValInt_dvd_iff 1 Z).mp (by simpa using hpZ)
    exact_mod_cast this.resolve_left hZ0
  have hcastdvd : ∀ p : ℕ, (p : ℤ) ∣ Z → (p : Zs) ∣ (Z : Zs) := fun p hpZ => by
    have := map_dvd (Int.castRingHom Zs) hpZ; simpa using this
  -- `v_p(Θ) = 0` at odd `p ∣ Z`
  have hΘodd : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ Z → padicValRat p Θ = 0 := by
    intro p hp hp2 hpZ
    have := Fact.mk hp
    obtain ⟨π, hπ, hπp⟩ := exists_prime_dvd_natCast p
    have hσp := star_dvd_natCast hπp
    have h1 := hlocal π hπ (hπp.trans (hcastdvd p hpZ))
    have h2 := hlocal (star π) (prime_star hπ) (hσp.trans (hcastdvd p hpZ))
    rw [Vge, le_vP_iff, Mult.vp_intCast hp2 hπ hπp hZ0] at h1
    rw [Vge, le_vP_iff, Mult.vp_intCast hp2 (prime_star hπ) hσp hZ0] at h2
    have hv2 : padicValRat p 2 = 0 := by
      rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd]
      · rfl
      intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hy : Θ - 2 = 0 ∨ (padicValInt p Z : ℤ) ≤ padicValRat p (Θ - 2) := by
      by_cases hy0 : (poleW R C)⁻¹ - 1 = 0
      · left; rw [← htr, hy0]; simp
      rcases Mult.vp_trace_ge hp2 hπ hπp (h1.resolve_left hy0) (h2.resolve_left hy0) with h | h
      · left; rwa [← htr]
      · right; rwa [← htr]
    by_cases h0 : Θ - 2 = 0
    · rw [show Θ = 2 by linarith, hv2]
    have hlt := hy.resolve_left h0
    have := hpZ1 p hp hpZ
    rw [show Θ = 2 + (Θ - 2) by ring, padicValRat.add_eq_of_lt (by rw [← show Θ = 2 + (Θ - 2) by ring]; exact hΘ)
      two_ne_zero h0 (by rw [hv2]; omega), hv2]
  -- `v₂(Θ) = 1`
  have h2Z : ((2 : ℕ) : ℤ) ∣ Z := Dvd.dvd.mul_right (by norm_num) F
  have hΘtwo : padicValRat 2 Θ = 1 := by
    have hsZ : sqrt2Z ∣ (Z : Zs) :=
      (show sqrt2Z ∣ ((2 : ℕ) : Zs) from ⟨sqrt2Z, by rw [Nat.cast_ofNat, two_eq_sqrt2Z_sq, sq]⟩).trans
        (hcastdvd 2 h2Z)
    have h1 := hlocal sqrt2Z prime_sqrt2Z hsZ
    rw [Vge, le_vP_iff, vS_int hZ0] at h1
    have hv2 : padicValRat 2 (2 : ℚ) = 1 := by
      have := padicValRat.self (p := 2) one_lt_two; simpa using this
    have hy : Θ - 2 = 0 ∨ (padicValInt 2 Z : ℤ) + 1 ≤ padicValRat 2 (Θ - 2) := by
      by_cases hy0 : (poleW R C)⁻¹ - 1 = 0
      · left; rw [← htr, hy0]; simp
      rcases vS_trace_ge (h1.resolve_left hy0) with h | h
      · left; rwa [← htr]
      · right; rwa [← htr]
    by_cases h0 : Θ - 2 = 0
    · rw [show Θ = 2 by linarith, hv2]
    have hlt := hy.resolve_left h0
    have := hpZ1 2 Nat.prime_two h2Z
    rw [show Θ = 2 + (Θ - 2) by ring, padicValRat.add_eq_of_lt (by rw [← show Θ = 2 + (Θ - 2) by ring]; exact hΘ)
      two_ne_zero h0 (by rw [hv2]; omega), hv2]
  -- the valuations of `R`
  have hRZ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ Z → padicValRat p R = padicValInt p Z := by
    intro p hp hpZ
    have := Fact.mk hp
    have hR₀v : padicValRat p (testR₀ η n) = padicValInt p Z := by
      rw [hR₀, padicValRat.mul hη0 hZK, padicValRat_of_sq_eq_one hη, padicValRat.of_int, zero_add]
    have ha0v : padicValRat p (1 - testR₀ η n * q ^ 2) = 0 := by
      by_cases hq0 : q = 0
      · rw [hq0]; simp
      have hX0 : testR₀ η n * q ^ 2 ≠ 0 := mul_ne_zero hR₀0 (pow_ne_zero 2 hq0)
      have hXv : 0 < padicValRat p (testR₀ η n * q ^ 2) := by
        rw [padicValRat.mul hR₀0 (pow_ne_zero 2 hq0), padicValRat.pow, hR₀v]
        have := hq p hp hpZ
        have := hpZ1 p hp hpZ
        push_cast; omega
      rw [sub_eq_add_neg, padicValRat.add_eq_of_lt (by rwa [← sub_eq_add_neg]) one_ne_zero
        (neg_ne_zero.mpr hX0) (by rw [padicValRat.one, padicValRat.neg]; exact hXv),
        padicValRat.one]
    rw [hRdef, padicValRat.mul hR₀0 (pow_ne_zero 2 ha0), padicValRat.pow, ha0v, hR₀v]
    simp
  have hRZ' : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ Z → Even (padicValRat p R) := by
    intro p hp hpZ
    have := Fact.mk hp
    rw [hRdef, padicValRat.mul hR₀0 (pow_ne_zero 2 ha0), padicValRat.pow, hR₀,
      padicValRat.mul hη0 hZK, padicValRat_of_sq_eq_one hη, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hpZ]
    exact ⟨padicValRat p (1 - η * Z * q ^ 2), by push_cast; ring⟩
  -- `v_p(Z) ≥ 6` for `p ∈ S₀`
  have hZ6 : ∀ p ∈ ({2, 3, 5, 7, 13} : Finset ℕ), 6 ≤ (padicValInt p Z : ℤ) := by
    intro p hp
    have hpp : p.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have := Fact.mk hpp
    rw [← padicValRat.of_int, hZdef, Int.cast_mul, padicValRat.mul (by norm_num)
      (Int.cast_ne_zero.mpr hF0), Int.cast_pow, padicValRat.pow, Int.cast_ofNat,
      padicValRat_2730 hp, padicValRat.of_int]
    push_cast; omega
  have hB : ∀ p : ℕ, p.Prime →
      padicValRat p (testB n κ n η q (2 * κ) (2 * κ * n)) = padicValRat p R - 2 * padicValRat p Θ := by
    intro p hp
    have := Fact.mk hp
    rw [testB, padicValRat.div hR0 (pow_ne_zero 2 hΘ), padicValRat.pow]; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hB 2 Nat.prime_two, hRZ 2 Nat.prime_two h2Z, hΘtwo]
    have := hZ6 2 (by simp); omega
  · intro p hp
    have hp' : p ∈ ({2, 3, 5, 7, 13} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢; tauto
    have hpp : p.Prime := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> norm_num
    have hp2 : p ≠ 2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp; omega
    have h6 := hZ6 p hp'
    have hpZ : (p : ℤ) ∣ Z := by
      have := Fact.mk hpp
      have h1 : (p : ℤ) ^ 1 ∣ Z := (padicValInt_dvd_iff (p := p) 1 Z).mpr (Or.inr (by omega))
      simpa using h1
    rw [hB p hpp, hRZ p hpp hpZ, hΘodd p hpp hp2 hpZ]; omega
  · apply isSquare_den_of
    intro p hp
    by_cases hpZ : (p : ℤ) ∣ Z
    · left
      rw [hB p hp, hRZ p hp hpZ]
      by_cases hp2 : p = 2
      · subst hp2; rw [hΘtwo]; have := hZ6 2 (by simp); omega
      · rw [hΘodd p hp hp2 hpZ]; have := hpZ1 p hp hpZ; omega
    · right
      rw [hB p hp]
      obtain ⟨m, hm⟩ := hRZ' p hp hpZ
      exact ⟨m - padicValRat p Θ, by omega⟩

end ZInQ.Assembly
