import ZInQKernel.Multiplication.Local.Analytic

/-!
# The formal logarithm of `y² = x³ + A x`: coefficients, convergence, isometry

Blueprint: `multiplication/local/formal-logarithm.md` (the series and its convergence),
`multiplication/local/logarithm-isometry.md` (part 1).

The invariant differential of `W : y² = x³ + A x`, expanded in `z = -x/y`, is
`dz / √(1 - 4 A z⁴) = Σ_j binom(2j, j) Aʲ z^{4j} dz` (`logarithm-series.md`), so the formal
logarithm is `log T = Σ_{r ≥ 1} b_{r-1} T^r / r` with `b_{4j} = binom(2j, j) Aʲ` and `b_i = 0`
for `4 ∤ i` (`invDiffCoeff`, `logCoeffA`, `formalLog`). For `E` (`A = -d²`) this is the binomial
series `Σ_j (-1)ʲ binom(2j, j) d^{2j} T^{4j+1}/(4j+1)`.

In a complete `ℤᵐ⁰`-valued field `K` of residue characteristic `p` with `v(p) = e`
(`ResidueChar K p e`) and `v(A) ≥ 0`:

* `summable_log`: the series converges for `v(t) > 0`; `evalLog A t` is its sum;
* `evalLog_isometry` (isometry, part 1): if `v(t) > e/(p - 1)` then `v(log t - t) > v(t)`, so
  `v(log t) = v(t)`.
-/

namespace ZInQ.Mult

open Filter Topology Finset WithZero

/-! ### The coefficients -/

/-- The coefficient `b_n` of `Tⁿ` in `1/√(1 - 4AT⁴)`: `binom(2j, j) Aʲ` if `n = 4j`, else `0`. -/
def invDiffCoeff {R : Type*} [CommRing R] (A : R) (n : ℕ) : R :=
  if n % 4 = 0 then (Nat.centralBinom (n / 4) : R) * A ^ (n / 4) else 0

/-- The expansion `Σ bₙ Tⁿ` of the invariant differential `dx/(2y) = dz/√(1 - 4Az⁴)`. -/
def invDiffSeries {R : Type*} [CommRing R] (A : R) : PowerSeries R := PowerSeries.mk (invDiffCoeff A)

/-- The coefficient `b_{r-1}/r` of `T^r` in the formal logarithm (`0` for `r = 0`). -/
def logCoeffA {F : Type*} [Field F] (A : F) (r : ℕ) : F :=
  if r = 0 then 0 else invDiffCoeff A (r - 1) / r

/-- The formal logarithm `log T = Σ_{r ≥ 1} b_{r-1} T^r / r` of `y² = x³ + A x`. -/
def formalLog {F : Type*} [Field F] (A : F) : PowerSeries F := PowerSeries.mk (logCoeffA A)

theorem invDiffCoeff_zero {R : Type*} [CommRing R] (A : R) : invDiffCoeff A 0 = 1 := by
  simp [invDiffCoeff]

theorem logCoeffA_one {F : Type*} [Field F] (A : F) : logCoeffA A 1 = 1 := by
  simp [logCoeffA, invDiffCoeff_zero]

theorem logCoeffA_zero {F : Type*} [Field F] (A : F) : logCoeffA A 0 = 0 := by
  simp [logCoeffA]

/-- `r · (coefficient of T^r) = b_{r-1}`, in characteristic zero. -/
theorem logCoeffA_mul {F : Type*} [Field F] [CharZero F] (A : F) {r : ℕ} (hr : r ≠ 0) :
    logCoeffA A r * r = invDiffCoeff A (r - 1) := by
  simp only [logCoeffA, hr, ↓reduceIte]
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hr)]

/-! ### Residue characteristic -/

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- `K` has residue characteristic `p` and `v(p) = e`: `v(p) = e` and `v(n) = 0` for `p ∤ n`. -/
structure ResidueChar (K : Type*) [Field K] [Valued K ℤᵐ⁰] (p e : ℕ) : Prop where
  val_p : vK K (p : K) = (e : ℤ)
  val_coprime : ∀ n : ℕ, ¬ p ∣ n → vK K (n : K) = 0

variable {p e : ℕ} [hp : Fact p.Prime]

theorem ResidueChar.val_natCast (h : ResidueChar K p e) {n : ℕ} (hn : n ≠ 0) :
    vK K (n : K) = ((e * padicValNat p n : ℕ) : ℤ) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.cast_mul, Nat.cast_pow, (vK K).map_mul, (vK K).map_pow, h.val_p, h.val_coprime m hm,
    padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero, add_zero]
  rw [← WithTop.coe_nsmul]; congr 1; push_cast; ring

theorem ResidueChar.natCast_ne_zero (h : ResidueChar K p e) {n : ℕ} (hn : n ≠ 0) : (n : K) ≠ 0 := by
  intro h0
  have := h.val_natCast hn
  rw [h0, (vK K).map_zero] at this
  exact WithTop.top_ne_coe this

/-! ### Elementary inequalities -/

/-- `(p - 1) v_p(r) ≤ r - 1` (from `p^{v_p(r)} ≤ r` and Bernoulli). -/
theorem padicValNat_bernoulli {r : ℕ} (hr : r ≠ 0) :
    ((p : ℤ) - 1) * padicValNat p r ≤ r - 1 := by
  have h1 : p ^ padicValNat p r ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) pow_padicValNat_dvd
  generalize padicValNat p r = k at h1 ⊢
  have h2 := one_add_le_pow_of_two_add_nonneg (R := ℤ) (a := (p : ℤ) - 1)
    (by have := hp.out.two_le; omega) k
  have h3 : ((1 + ((p : ℤ) - 1)) ^ k) ≤ r := by
    rw [show (1 + ((p : ℤ) - 1)) = (p : ℤ) by ring]; exact_mod_cast h1
  linarith

theorem sq_le_two_pow_add (k : ℕ) : k * k ≤ 2 ^ k + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := Nat.mul_le_pow (show 2 ≠ 1 by norm_num) k
    rw [pow_succ]
    nlinarith

/-- `2 e v_p(r) ≤ r + 4e² + 2e`. -/
theorem two_mul_padicValNat_le (r e : ℕ) (hr : r ≠ 0) :
    2 * e * padicValNat p r ≤ r + 4 * e ^ 2 + 2 * e := by
  set k := padicValNat p r
  have h1 : p ^ k ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) pow_padicValNat_dvd
  have h2 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.out.two_le k
  have h3 := sq_le_two_pow_add k
  by_cases hk : k ≤ 2 * e + 1
  · nlinarith
  · push Not at hk
    nlinarith

/-! ### Valuations of the terms -/

theorem vge_invDiffCoeff (hA : 0 ≤ vK K A) (n : ℕ) : Vge (vK K) 0 (invDiffCoeff A n) := by
  unfold invDiffCoeff
  split_ifs
  · have := (vge_natCast (v := vK K) (Nat.centralBinom (n / 4))).mul ((show Vge (vK K) 0 A from hA).pow (n / 4))
    simpa using this
  · exact Vge.zero 0

/-- `v(b_{r-1} t^r / r) ≥ r v(t) - e v_p(r)`. -/
theorem vge_logTerm (h : ResidueChar K p e) {A t : K} (hA : 0 ≤ vK K A) {m : ℤ}
    (ht : Vge (vK K) m t) (r : ℕ) :
    Vge (vK K) (r * m - e * padicValNat p r) (logCoeffA A r * t ^ r) := by
  by_cases hr : r = 0
  · subst hr; simp [logCoeffA]; exact Vge.zero _
  simp only [logCoeffA, hr, ↓reduceIte]
  rw [div_mul_eq_mul_div]
  have hnum := (vge_invDiffCoeff hA (r - 1)).mul (ht.pow r)
  have := hnum.div_val' (h.val_natCast hr)
  refine this.mono ?_
  push_cast; omega

/-! ### Convergence -/

/-- **Convergence of the formal logarithm** on `v(t) > 0`. -/
theorem summable_log [CompleteSpace K] (h : ResidueChar K p e) {A t : K} (hA : 0 ≤ vK K A)
    (ht : 1 ≤ vK K t) : Summable fun r => logCoeffA A r * t ^ r := by
  refine summable_of_vK fun M => ?_
  rw [eventually_atTop]
  refine ⟨(2 * M + 4 * e ^ 2 + 2 * e).toNat + 1, fun r hr => ?_⟩
  have hr0 : r ≠ 0 := by omega
  have hterm := vge_logTerm h hA (show Vge (vK K) 1 t from ht) r
  refine (hterm.mono ?_)
  have := two_mul_padicValNat_le (p := p) r e hr0
  have hr' : (2 * M + 4 * e ^ 2 + 2 * e) < r := by omega
  generalize padicValNat p r = k at this ⊢
  have h' : (2 * e * k : ℤ) ≤ r + 4 * e ^ 2 + 2 * e := by exact_mod_cast this
  nlinarith

/-- The sum `log t = Σ_r b_{r-1} t^r / r` (meaningful for `v(t) > 0`). -/
noncomputable def evalLog (A t : K) : K := ∑' r, logCoeffA A r * t ^ r

theorem evalLog_sub_self [CompleteSpace K] (h : ResidueChar K p e) {A t : K} (hA : 0 ≤ vK K A)
    (ht : 1 ≤ vK K t) :
    evalLog A t - t = ∑' r, logCoeffA A (r + 2) * t ^ (r + 2) := by
  have hs := summable_log h hA ht
  rw [evalLog, ← hs.sum_add_tsum_nat_add 2]
  rw [Finset.sum_range_succ, Finset.sum_range_one, logCoeffA_zero, logCoeffA_one]
  ring

/-- **The isometry range of the logarithm** (part 1): if `v(t) > e/(p - 1)`, that is
`(p - 1) v(t) > e`, then `v(log t - t) > v(t)`, hence `v(log t) = v(t)`. -/
theorem evalLog_isometry [CompleteSpace K] (h : ResidueChar K p e) {A t : K} (hA : 0 ≤ vK K A)
    {m : ℤ} (ht : vK K t = m) (hm : (e : ℤ) < ((p : ℤ) - 1) * m) :
    vK K t < vK K (evalLog A t - t) ∧ vK K (evalLog A t) = vK K t := by
  have hp1 : (1 : ℤ) ≤ (p : ℤ) - 1 := by have := hp.out.two_le; omega
  have hm1 : 1 ≤ m := by
    by_contra hc; push Not at hc; nlinarith
  have ht1 : 1 ≤ vK K t := by rw [ht]; exact_mod_cast hm1
  have hs := summable_log h hA ht1
  have hterm : ∀ r : ℕ, vK K t < vK K (logCoeffA A (r + 2) * t ^ (r + 2)) := by
    intro r
    have h1 := vge_logTerm h hA (Vge.of_eq ht) (r + 2)
    have h2 := padicValNat_bernoulli (p := p) (r := r + 2) (by omega)
    rw [ht]
    refine lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (lt_add_one m)) (h1.mono ?_)
    generalize padicValNat p (r + 2) = k at h2 ⊢
    have h3 : ((r + 2 : ℕ) : ℤ) = (r : ℤ) + 2 := by push_cast; ring
    rw [h3] at h2 ⊢
    have h4 : (e : ℤ) * ((p : ℤ) - 1) * k ≤ e * ((r : ℤ) + 1) := by
      have : (0 : ℤ) ≤ e := by positivity
      nlinarith
    have h5 : (e : ℤ) * ((r : ℤ) + 1) < ((p : ℤ) - 1) * m * ((r : ℤ) + 1) := by
      have : (0 : ℤ) < (r : ℤ) + 1 := by positivity
      nlinarith
    have h6 : ((p : ℤ) - 1) * (e * k) < ((p : ℤ) - 1) * (((r : ℤ) + 2) * m - m) := by
      nlinarith
    have h7 : (e : ℤ) * k < ((r : ℤ) + 2) * m - m := lt_of_mul_lt_mul_left h6 (by omega)
    omega
  have hlt : vK K t < vK K (evalLog A t - t) := by
    rw [evalLog_sub_self h hA ht1]
    exact lt_vK_tsum ((summable_nat_add_iff (f := fun r => logCoeffA A r * t ^ r) 2).mpr hs) hterm
  refine ⟨hlt, ?_⟩
  have := (vK K).map_add_eq_of_lt_left hlt
  rwa [add_sub_cancel] at this

end ZInQ.Mult
