import ZInQKernel.Size.FormalMultiple.OddCoefficients
import ZInQKernel.Size.FormalMultiple.FormalMul
import ZInQKernel.Multiplication.Local.Dyadic
import ZInQKernel.Syntax.Constants.Fixed

/-!
# A successful formal multiple

Blueprint: `size/formal-multiple/formal-multiple-existence.md`.

For every `N ≥ 1` there is `m` with `1 ≤ m ≤ N¹⁰` satisfying the formal condition: the
normalized representation `(a + b s)/c` of `ξ([m]P₀)` has `N⁴ ∣ a`, `N⁴ ∣ b`, `gcd(c, N) = 1`
(`exists_formal_multiple`). Hence `1 ≤ LFM(N) ≤ N¹⁰` and `LFM(N)` satisfies the condition
(`leastFormalMultiple_bounds`), and `1 ≤ M₀ ≤ N_s¹⁰` whenever `N_s ≥ 1` (`M0_bounds`).

Proof: `m = N⁴ m₀` with `m₀` from the reduction orders.

* At a prime `π` above an odd `p ∣ N`: `[m₀]P₀ ∈ E₁(π)` and `v_π(p) = 1`, so
  `[m]P₀ ∈ E_{1 + 4 v_p(N)}(π)` (`nsmul_mem_formalFilt_of_val`) and
  `v_π(ξ) ≥ 2 + 8 v_p(N)`; then `v_p(u₀), v_p(u₁) ≥ 4 v_p(N)` (`padicValRat_coords_ge`).
* At `(s)` (if `2 ∣ N`): `P₀ ∈ E₃(s)` and `v_s(2) = 2`, so `[m]P₀ ∈ E_{3 + 8 v₂(N)}(s)`,
  `v_s(ξ) ≥ 6 + 16 v₂(N)`, and the formula `v_s(u₀ + u₁ s) = min(2 v₂(u₀), 2 v₂(u₁) + 1)` gives
  `v₂(u₀), v₂(u₁) ≥ 4 v₂(N)`.
* Normalization: these bounds give `p ∤ den uᵢ`, hence `gcd(c, N) = 1` for
  `c = lcm(den u₀, den u₁)`, and `v_p(a) = v_p(u₀) ≥ 4 v_p(N)` (`formalCondition_of_padicValRat`).

No property of `P₀` beyond these is used (in particular not that `P₀` has infinite order).
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine Syntax

/-! ### Normalization -/

/-- A rational number with `v_p ≥ 0` has denominator prime to `p`. -/
theorem not_dvd_den_of_nonneg {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0)
    (h : 0 ≤ padicValRat p q) : ¬p ∣ q.den := by
  intro hden
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  rw [padicValRat_def] at h
  have hpnum : ¬(p : ℤ) ∣ q.num := by
    intro h2
    have h2' : p ∣ q.num.natAbs := Int.ofNat_dvd_left.mp h2
    have := Nat.dvd_gcd h2' hden
    rw [q.reduced.gcd_eq_one] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  have h1 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hpnum
  have h2 : padicValNat p q.den ≠ 0 := by
    rw [Ne, padicValNat.eq_zero_iff, not_or, not_or, not_not]
    exact ⟨hp.out.one_lt.ne', q.den_nz, hden⟩
  omega

/-- If `v_p(q) ≥ 0` at every prime `p ∣ N`, the denominator of `q` is prime to `N`. -/
theorem den_coprime {N : ℕ} (hN0 : N ≠ 0) {q : ℚ}
    (h : ∀ p ∈ N.primeFactors, q ≠ 0 → 0 ≤ padicValRat p q) : Nat.Coprime q.den N := by
  by_cases hq : q = 0
  · subst hq; simp
  refine Nat.coprime_of_dvd fun p hp hpd hpN => ?_
  have : Fact p.Prime := ⟨hp⟩
  exact not_dvd_den_of_nonneg hq (h p (Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩) hq) hpd

/-- **Normalization.** If `v_p(u₀), v_p(u₁) ≥ 4 v_p(N)` for every prime `p ∣ N` (for the
nonzero coordinates), then the normalized representation `(a, b, c)` of `u = u₀ + u₁ s` has
`N⁴ ∣ a`, `N⁴ ∣ b` and `gcd(c, N) = 1`. -/
theorem formalCondition_of_padicValRat {N : ℕ} (hN : 1 ≤ N) (u : K0)
    (h : ∀ p ∈ N.primeFactors,
      (u.re ≠ 0 → 4 * (padicValNat p N : ℤ) ≤ padicValRat p u.re) ∧
        (u.im ≠ 0 → 4 * (padicValNat p N : ℤ) ≤ padicValRat p u.im)) :
    (N : ℤ) ^ 4 ∣ (normalizedRep u).1 ∧ (N : ℤ) ^ 4 ∣ (normalizedRep u).2.1 ∧
      Nat.Coprime (normalizedRep u).2.2 N := by
  have hnn : ∀ q : ℚ, (∀ p ∈ N.primeFactors, q ≠ 0 → 4 * (padicValNat p N : ℤ) ≤
      padicValRat p q) → ∀ p ∈ N.primeFactors, q ≠ 0 → 0 ≤ padicValRat p q :=
    fun q hq p hp hq0 => le_trans (by positivity) (hq p hp hq0)
  have hre := fun p hp => (h p hp).1
  have him := fun p hp => (h p hp).2
  set L := Nat.lcm u.re.den u.im.den with hL
  have hcop : Nat.Coprime L N := by
    refine Nat.Coprime.coprime_dvd_left (Nat.lcm_dvd_mul _ _) (Nat.Coprime.mul_left ?_ ?_)
    · exact den_coprime (by omega) (hnn _ hre)
    · exact den_coprime (by omega) (hnn _ him)
  -- the divisibility of a coordinate
  have key : ∀ q : ℚ, (∀ p ∈ N.primeFactors, q ≠ 0 → 4 * (padicValNat p N : ℤ) ≤
      padicValRat p q) → q.den ∣ L → (N : ℤ) ^ 4 ∣ q.num * ((L / q.den : ℕ) : ℤ) := by
    intro q hq hdL
    by_cases hq0 : q = 0
    · subst hq0; simp
    have hL0 : L ≠ 0 := Nat.lcm_ne_zero u.re.den_nz u.im.den_nz
    have hc0 : L / q.den ≠ 0 := by
      intro h0
      have := Nat.div_mul_cancel hdL
      rw [h0, zero_mul] at this; exact hL0 this.symm
    have ha0 : q.num * ((L / q.den : ℕ) : ℤ) ≠ 0 :=
      mul_ne_zero (Rat.num_ne_zero.mpr hq0) (by exact_mod_cast hc0)
    -- `a = q L` in `ℚ`
    have haq : ((q.num * ((L / q.den : ℕ) : ℤ) : ℤ) : ℚ) = q * L := by
      have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdL hd]
      nth_rw 3 [← Rat.num_div_den q]
      field_simp
    have : ((N ^ 4 : ℕ) : ℤ) ∣ q.num * ((L / q.den : ℕ) : ℤ) := Int.natCast_dvd.mpr ?_
    · simpa using this
    refine (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ (by omega))
      (Int.natAbs_ne_zero.mpr ha0)).mp fun p hp => ?_
    have := Fact.mk hp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hpN : p ∣ N
    · have hpm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, by omega⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      have hpL : ¬p ∣ L := fun hpL =>
        hp.one_lt.ne' (Nat.dvd_one.mp (by
          have := Nat.dvd_gcd hpL hpN; rwa [hcop.gcd_eq_one] at this))
      have hval : (padicValNat p (q.num * ((L / q.den : ℕ) : ℤ)).natAbs : ℤ) =
          padicValRat p q := by
        rw [← padicValInt, ← padicValRat.of_int, haq,
          padicValRat.mul hq0 (by exact_mod_cast hL0), padicValRat.of_nat,
          padicValNat.eq_zero_of_not_dvd hpL]
        simp
      have := hq p hpm hq0
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hpN]; simp
  refine ⟨key _ hre (Nat.dvd_lcm_left _ _), key _ him (Nat.dvd_lcm_right _ _), hcop⟩

/-! ### Valuations of `ξ` in the formal neighbourhood -/

/-- In `E_r(π)`, `v_π(ξ) = v_π(1/x) = 2 v_π(z) ≥ 2r`. -/
theorem vP_xi_ge {π : Zs} (hπ : Prime π) {r : ℤ} {Q : genCurve.toAffine.Point}
    (hQ : Q ∈ Mult.formalFilt (-genD ^ 2) (vP_A_nonneg hπ (vge_neg_genD_sq _ hπ)) r) :
    ((2 * r : ℤ) : WithTop ℤ) ≤ Mult.vP π hπ (xi Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [show xi Point.zero = 0 from rfl, (Mult.vP π hπ).map_zero]; exact le_top
  obtain ⟨N, -, hx, -, -, hz, -⟩ := Mult.formal_val_x_y (vP_A_nonneg hπ (vge_neg_genD_sq _ hπ)) h hQ.1
  have hrN : r ≤ N := by have := hQ.2.trans (le_of_eq hz); exact_mod_cast this
  rw [xi_some, Mult.val_inv_coe hx]
  exact_mod_cast (show 2 * r ≤ -(-2 * N) by omega)

theorem vP_natCast_of_dvd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π)
    (hπp : π ∣ (p : Zs)) : Mult.vP π hπ (p : K0) = ((1 : ℤ) : WithTop ℤ) := by
  rw [Mult.vP_apply hπ (Nat.cast_ne_zero.mpr hp.out.ne_zero), Mult.vp_natCast_self hp2 hπ hπp]

theorem vS_two' : Mult.vS ((2 : ℕ) : K0) = ((2 : ℤ) : WithTop ℤ) := by
  rw [Mult.vP_apply _ (by norm_num), Nat.cast_ofNat, vS_two]

/-- Split `N = pᵏ N'` with `p ∤ N'`, `k = v_p(N)`. -/
theorem exists_split {N p : ℕ} (hN : N ≠ 0) (hp : p.Prime) :
    ∃ N' : ℕ, N = p ^ padicValNat p N * N' := by
  obtain ⟨k, N', hN', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.one_lt.ne'
  have : Fact p.Prime := ⟨hp⟩
  have hN0 : N' ≠ 0 := by rintro rfl; simp at hN'
  refine ⟨N', ?_⟩
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hN0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hN', add_zero]

/-! ### The successful index -/

/-- **A successful formal multiple.** For every `N ≥ 1` there is `m` with `1 ≤ m ≤ N¹⁰`
satisfying the formal condition defining `LFM(N)`. -/
theorem exists_formal_multiple (N : ℕ) (hN : 1 ≤ N) :
    ∃ m, 1 ≤ m ∧ m ≤ N ^ 10 ∧ FormalCondition N m := by
  obtain ⟨m₀, hm₀1, hm₀le, hm₀⟩ := exists_reduction_multiple N hN
  have hN4 : 1 ≤ N ^ 4 := Nat.one_le_pow _ _ hN
  refine ⟨N ^ 4 * m₀, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩
  · calc N ^ 4 * m₀ ≤ N ^ 4 * N ^ 6 := Nat.mul_le_mul_left _ hm₀le
      _ = N ^ 10 := by ring
  apply formalCondition_of_padicValRat hN
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have := Fact.mk hpp
  obtain ⟨N', hN'⟩ := exists_split (show N ≠ 0 by omega) hpp
  set k := padicValNat p N
  have hm : N ^ 4 * m₀ = p ^ (4 * k) * (N' ^ 4 * m₀) := by
    nth_rw 1 [hN']; ring
  by_cases hp2 : p = 2
  · -- the prime `(s)` above `2`
    subst hp2
    have hmem := nsmul_mem_formalFilt_of_val Mult.vS_genA_nonneg vS_two' (by norm_num) (by norm_num)
      Mult.genP0_mem_formalFilt_three (4 * k) (N' ^ 4 * m₀)
    rw [← hm] at hmem
    have hv := vP_xi_ge prime_sqrt2Z (r := 3 + (4 * k : ℕ) * 2)
      (Q := (N ^ 4 * m₀) • genP0) hmem
    set u := xi ((N ^ 4 * m₀) • genP0)
    by_cases hu : u = 0
    · rw [hu]; simp
    have hu' : u.re ≠ 0 ∨ u.im ≠ 0 := by
      by_contra hc; push Not at hc; exact hu (K0.ext_iff'.mpr ⟨hc.1, hc.2⟩)
    rw [Mult.vP_apply _ hu] at hv
    have hv' : 2 * (3 + ((4 * k : ℕ) : ℤ) * 2) ≤ vp sqrt2Z u := by exact_mod_cast hv
    have hcomp : (u.re ≠ 0 → 2 * (3 + ((4 * k : ℕ) : ℤ) * 2) ≤ 2 * padicValRat 2 u.re) ∧
        (u.im ≠ 0 → 2 * (3 + ((4 * k : ℕ) : ℤ) * 2) ≤ 2 * padicValRat 2 u.im + 1) := by
      by_cases h0 : u.re = 0
      · have hu1 : u.im ≠ 0 := hu'.resolve_left (not_not.mpr h0)
        have e : u = (u.im : K0) * sqrt2 := by ext <;> simp [sqrt2, h0]
        rw [e, vS_rat_mul_sqrt2 hu1] at hv'
        exact ⟨fun h => absurd h0 h, fun _ => hv'⟩
      by_cases h1 : u.im = 0
      · have e : u = (u.re : K0) := by ext <;> simp [h1]
        rw [e, vS_rat h0] at hv'
        exact ⟨fun _ => hv', fun h => absurd h1 h⟩
      · rw [show u = ⟨u.re, u.im⟩ from rfl, vS_formula h0 h1] at hv'
        exact ⟨fun _ => hv'.trans (min_le_left _ _), fun _ => hv'.trans (min_le_right _ _)⟩
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · have := hcomp.1 h0; push_cast at this; omega
    · have := hcomp.2 h0; push_cast at this; omega
  · -- the primes above an odd `p`
    have key : ∀ π : Zs, ∀ hπ : Prime π, π ∣ (p : Zs) →
        (((2 + 8 * k : ℤ)) : WithTop ℤ) ≤ Mult.vP π hπ (xi ((N ^ 4 * m₀) • genP0)) := by
      intro π hπ hπp
      have h1 := hm₀ p hp hp2 π hπ hπp
      rw [E1sub_eq_formalNbhd, natCast_zsmul] at h1
      have hmem := nsmul_mem_formalFilt_of_val _ (vP_natCast_of_dvd hp2 hπ hπp) (by norm_num)
        (by norm_num) h1 (4 * k) (N' ^ 4)
      have e : (N ^ 4 * m₀) • genP0 = (p ^ (4 * k) * N' ^ 4) • (m₀ • genP0) := by
        rw [smul_smul, hm]; ring_nf
      rw [e]
      have := vP_xi_ge hπ hmem
      have h2 : ((2 + 8 * k : ℤ) : WithTop ℤ) = ((2 * (1 + ((4 * k : ℕ) : ℤ) * 1) : ℤ) :
          WithTop ℤ) := by
        congr 1; push_cast; ring
      exact h2.trans_le this
    obtain ⟨h1, h2⟩ := padicValRat_coords_ge hp2 _ _ key
    exact ⟨fun h0 => by have := h1 h0; omega, fun h0 => by have := h2 h0; omega⟩

/-- **The least formal multiple succeeds**: `1 ≤ LFM(N) ≤ N¹⁰` for `N ≥ 1`. -/
theorem leastFormalMultiple_bounds (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ leastFormalMultiple N ∧ leastFormalMultiple N ≤ N ^ 10 := by
  obtain ⟨m, hm1, hmle, hm⟩ := exists_formal_multiple N hN
  obtain ⟨h1, -, h3⟩ := Syntax.leastFormalMultiple_spec ⟨m, hm1, hm⟩
  exact ⟨h1, (h3 m hm1 hm).trans hmle⟩

/-- `LFM(N)` satisfies the formal condition for `N ≥ 1`. -/
theorem leastFormalMultiple_formalCondition (N : ℕ) (hN : 1 ≤ N) :
    FormalCondition N (leastFormalMultiple N) := by
  obtain ⟨m, hm1, -, hm⟩ := exists_formal_multiple N hN
  exact (Syntax.leastFormalMultiple_spec ⟨m, hm1, hm⟩).2.1

/-- **`M₀` is a successful index**: if `N_s ≥ 1`, then `1 ≤ M₀ ≤ N_s¹⁰` and `M₀` satisfies
the formal condition. -/
theorem M0_bounds (h : 1 ≤ Ns) : 1 ≤ M0 ∧ M0 ≤ Ns ^ 10 ∧ FormalCondition Ns M0 := by
  rw [M0_eq]
  exact ⟨(leastFormalMultiple_bounds Ns h).1, (leastFormalMultiple_bounds Ns h).2,
    leastFormalMultiple_formalCondition Ns h⟩

end ZInQ.Size
