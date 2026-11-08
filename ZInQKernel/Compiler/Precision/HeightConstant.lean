import ZInQKernel.Hypotheses.Height

/-!
# The precision height constant

Blueprint: `compiler/natural/precision/precision-height-constant.md` and
`compiler/natural/precision/precision-height-constant-value.md`.

The natural numbers `F₀ = 324!`, `D`, `G₀`, `E₀`, `B_cm`, `C_cm` are the hypothesis file's
`heightF0`, `heightD`, `heightG0`, `heightE0`, `heightBcm`, `heightCcm`; this file adds
`Q₀ = D^(D E₀)`, the precision constant `A⁽⁰⁾_ht = 2·10¹³ max(1, C_cm, Q₀¹⁷)` and the precision
bound `𝓑(n, κ) = A⁽⁰⁾_ht |κ F(n)|²⁴`. None of them is ever evaluated: every statement below is
proved symbolically.
-/

namespace ZInQ.Compiler.Precision

/-! ### Unfolding the hypothesis-file constants

The kernel cannot check `heightD = F₀ · 3^(256 F₀⁴)` by unfolding `heightD`: comparing the
constant with an application of `*` makes it evaluate `3 ^ (256 F₀⁴)`. When it compares two
definitions of the same definitional height it unfolds both, so each constant is first matched
with a function of the same height whose body, after `let`-elimination, is the constant's body.
The `let` binding of an unused constant only fixes that height. -/

/-- `D` as a function of `F₀` (same height as `heightD`). -/
def degFn (f : ℕ) : ℕ := f * 3 ^ (256 * f ^ 4)

/-- `E₀` as a function of `D` (same height as `heightE0`). -/
noncomputable def e0Fn (d : ℕ) : ℕ :=
  let _anchor := heightD
  10 * (d * heightG0) ^ 2

/-- `B_cm` as a function of `D` (same height as `heightBcm`). -/
noncomputable def bcmFn (d : ℕ) : ℕ :=
  let _anchor := heightD
  d ^ 2 * 3 ^ (21000 * d ^ 2) + 1

/-- `C_cm` as a function of `D` and `B_cm` (same height as `heightCcm`). -/
noncomputable def ccmFn (d b : ℕ) : ℕ :=
  let _anchor := heightBcm
  2 * b + 4096 * (1028 + 5 * d + 84000 * d ^ 2)

/-- `Q = D^(D E)`. -/
def qFn (d e : ℕ) : ℕ := d ^ (d * e)

/-- `2·10¹³ · max(1, C, Q¹⁷)`. -/
def h6Fn (c q : ℕ) : ℕ := 2 * 10 ^ 13 * max 1 (max c (q ^ 17))

theorem heightF0_eq : heightF0 = Nat.factorial 324 := rfl

theorem heightD_eq_degFn : heightD = degFn heightF0 := rfl
theorem heightE0_eq_e0Fn : heightE0 = e0Fn heightD := rfl
theorem heightBcm_eq_bcmFn : heightBcm = bcmFn heightD := rfl
theorem heightCcm_eq_ccmFn : heightCcm = ccmFn heightD heightBcm := rfl

theorem degFn_eq (f : ℕ) : degFn f = f * 3 ^ (256 * f ^ 4) := rfl
theorem e0Fn_eq (d : ℕ) : e0Fn d = 10 * (d * heightG0) ^ 2 := rfl
theorem bcmFn_eq (d : ℕ) : bcmFn d = d ^ 2 * 3 ^ (21000 * d ^ 2) + 1 := rfl
theorem ccmFn_eq (d b : ℕ) : ccmFn d b = 2 * b + 4096 * (1028 + 5 * d + 84000 * d ^ 2) := rfl

theorem heightD_eq : heightD = heightF0 * 3 ^ (256 * heightF0 ^ 4) := by
  rw [heightD_eq_degFn, degFn_eq]

theorem heightE0_eq : heightE0 = 10 * (heightD * heightG0) ^ 2 := by
  rw [heightE0_eq_e0Fn, e0Fn_eq]

theorem heightBcm_eq : heightBcm = heightD ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1 := by
  rw [heightBcm_eq_bcmFn, bcmFn_eq]

theorem heightCcm_eq :
    heightCcm = 2 * heightBcm + 4096 * (1028 + 5 * heightD + 84000 * heightD ^ 2) := by
  rw [heightCcm_eq_ccmFn, ccmFn_eq]

/-- `Q₀ = D^(D E₀)`, a natural number. -/
noncomputable def Q0 : ℕ := qFn heightD heightE0

/-- The precision height constant `A⁽⁰⁾_ht = 2·10¹³ · max(1, C_cm, Q₀¹⁷)`. -/
noncomputable def A0 : ℕ := h6Fn heightCcm Q0

theorem Q0_eq : Q0 = heightD ^ (heightD * heightE0) := by rw [Q0, qFn]

theorem A0_eq : A0 = 2 * 10 ^ 13 * max 1 (max heightCcm (Q0 ^ 17)) := by rw [A0, h6Fn]

/-- `F(u) = u(u+15)(u+20)(u+24)(u+30)(u+60)`. -/
def sixF (u : ℤ) : ℤ := u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)

/-- The precision bound `𝓑(n, κ) = A⁽⁰⁾_ht |κ F(n)|²⁴`. -/
noncomputable def bound (n κ : ℤ) : ℕ := A0 * (κ * sixF n).natAbs ^ 24

/-- The six contact values `𝒞 = {0, -15, -20, -24, -30, -60}` as integers. -/
def contacts : Finset ℤ := {0, -15, -20, -24, -30, -60}

/-- `F(n) = 0` exactly when `n ∈ 𝒞`. -/
theorem sixF_eq_zero_iff (n : ℤ) : sixF n = 0 ↔ n ∈ contacts := by
  simp only [sixF, mul_eq_zero, contacts, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- An integer lies in `𝒞 ⊆ ℤ` exactly when its image lies in the hypothesis file's
`contactSet ⊆ ℚ`. -/
theorem cast_mem_contactSet_iff (n : ℤ) : (n : ℚ) ∈ contactSet ↔ n ∈ contacts := by
  simp only [contactSet, contacts, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h | h | h) <;>
      [left; (right; left); (right; right; left); (right; right; right; left);
        (right; right; right; right; left); (right; right; right; right; right)] <;>
      exact_mod_cast h
  · rintro (h | h | h | h | h | h) <;> subst h <;> norm_num

theorem A0_pos : 0 < A0 := by
  rw [A0_eq]; positivity

/-! ### The precision constant is the six-contact constant -/

/-- The primes at most `324`, the set `S_ht`. -/
def heightPrimes : Finset ℕ := (Finset.range 325).filter Nat.Prime

theorem mem_heightPrimes {p : ℕ} : p ∈ heightPrimes ↔ p.Prime ∧ p ≤ 324 := by
  simp only [heightPrimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]

theorem heightPrimes_le {p : ℕ} (hp : p ∈ heightPrimes) : p ≤ 324 :=
  (mem_heightPrimes.mp hp).2

/-- `324! > 10¹²`, through `20! > 10¹²`. -/
theorem ten_pow_twelve_lt_heightF0 : 10 ^ 12 < heightF0 :=
  heightF0_eq ▸ lt_of_lt_of_le (by decide : 10 ^ 12 < Nat.factorial 20) (Nat.factorial_le (by norm_num))

theorem heightF0_le_heightD : heightF0 ≤ heightD := by
  rw [heightD_eq]
  exact Nat.le_mul_of_pos_right _ (by positivity)

theorem ten_pow_twelve_le_heightD : 10 ^ 12 ≤ heightD :=
  ten_pow_twelve_lt_heightF0.le.trans heightF0_le_heightD

theorem le_heightD_of_mem_heightPrimes {p : ℕ} (hp : p ∈ heightPrimes) : p ≤ heightD :=
  (heightPrimes_le hp).trans (le_trans (by norm_num) ten_pow_twelve_le_heightD)

/-- `max(D, max S_ht, 10¹²) = D`. -/
theorem max_heightD_heightPrimes :
    max (heightD : ℝ) (max ((heightPrimes.sup id : ℕ) : ℝ) ((10 : ℝ) ^ 12)) = heightD := by
  apply max_eq_left
  apply max_le
  · exact_mod_cast Finset.sup_le fun p hp => le_heightD_of_mem_heightPrimes hp
  · exact_mod_cast ten_pow_twelve_le_heightD

/-- `R = D` is an admissible argument of the six-contact estimate for `S_ht`. -/
theorem heightD_admissible :
    (∀ p ∈ heightPrimes, p.Prime) ∧ (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ heightPrimes) ∧
      (heightD : ℝ) ≤ heightD ∧ (∀ p ∈ heightPrimes, (p : ℝ) ≤ heightD) ∧
      (10 : ℝ) ^ 12 ≤ heightD :=
  ⟨fun _ hp => (mem_heightPrimes.mp hp).1, fun _ hp h => mem_heightPrimes.mpr ⟨hp, h⟩, le_rfl,
    fun _ hp => by exact_mod_cast le_heightD_of_mem_heightPrimes hp,
    by exact_mod_cast ten_pow_twelve_le_heightD⟩

/-- The real power `Q_D = D^(D E₀)` is the natural power `Q₀`. -/
theorem heightQ_heightD : heightQ (heightD : ℝ) = (Q0 : ℝ) := by
  rw [heightQ, Q0_eq, Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_mul]

/-- `H₆(S_ht) = H₆(S_ht; D) = A⁽⁰⁾_ht`. -/
theorem A0_eq_heightH6 : (A0 : ℝ) = heightH6 (heightD : ℝ) := by
  rw [heightH6, heightQ_heightD, A0_eq]
  simp only [Nat.cast_mul, Nat.cast_max, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]

/-- `𝓑(n, κ) = H₆(S_ht) |κ F(n)|²⁴`. -/
theorem bound_eq_heightH6 (n κ : ℤ) :
    (bound n κ : ℝ) = heightH6 (heightD : ℝ) * |((κ * sixF n : ℤ) : ℝ)| ^ 24 := by
  rw [bound, ← A0_eq_heightH6, Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]

/- The six-contact estimate at `S = S_ht`, `R = D`, `sixContact_at_heightPrimes`, is derived from
the minimal hypothesis `SixContactMin` in `ZInQKernel/Hypotheses/HeightMin.lean`: its statement
names the multiplication prime set `S_mul`, which is defined downstream of this file. -/

end ZInQ.Compiler.Precision
