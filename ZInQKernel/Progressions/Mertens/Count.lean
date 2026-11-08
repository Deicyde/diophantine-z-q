import ZInQKernel.Progressions.Mertens.Orthogonality
import ZInQKernel.Progressions.Mertens.Principal

/-!
# The residue-class count (plan step 4.4)

Prime powers `p^k` with `k ≥ 2` and `p^k > y` contribute at most
`E(y) = (log s + 2 + 2 log 4)/s` (`s = ⌊√y⌋`) to `S_a(x) − S_a(y)`, and each prime `p > y` at
most `log y / y` (`y ≥ 3`). With the principal-character lower bound and a bound `B` on `‖S_χ‖`
for `χ ≠ 1`, this gives at least 22 primes `p ≡ a (mod q)` with `q^8 < p ≤ q^8 · exp(5qB)`.
-/

namespace ZInQ.Progressions

open Finset Real
open ArithmeticFunction hiding log

variable {q : ℕ}

/-- `S_a(x) − S_a(Y) = Σ_{Y < n ≤ x, n ≡ a} Λ(n)/n` for a natural number `Y ≤ x`. -/
lemma classSum_sub_classSum_nat (a : ZMod q) {x : ℝ} {Y : ℕ} (hY : (Y : ℝ) ≤ x) :
    classSum a x - classSum a Y = ∑ n ∈ Ioc Y ⌊x⌋₊ with ((n : ℕ) : ZMod q) = a, Λ n / n := by
  have hYM : Y ≤ ⌊x⌋₊ := Nat.le_floor hY
  rw [classSum, classSum, Nat.floor_natCast, sum_filter, sum_filter, sum_filter,
    ← sum_Ioc_consecutive _ (Nat.zero_le Y) hYM]
  ring

/-- `log t / t ≤ log y / y` for `3 ≤ y ≤ t`. -/
lemma log_div_self_le_of_three_le {y t : ℝ} (hy : 3 ≤ y) (hyt : y ≤ t) :
    Real.log t / t ≤ Real.log y / y := by
  have he : exp 1 ≤ 3 := by linarith [exp_one_lt_d9]
  exact log_div_self_antitoneOn (Set.mem_Ici.mpr (he.trans hy))
    (Set.mem_Ici.mpr (he.trans (hy.trans hyt))) hyt

/-- **Upper bound for the class sum over `(Y, M]`**: each prime contributes at most
`log Y / Y` (for `Y ≥ 3`), and the prime powers `p^k`, `k ≥ 2`, at most
`E(Y) = (log s + 2 + 2 log 4)/s` in total, where `s = ⌊√Y⌋`. -/
theorem sum_Ioc_classSum_le (a : ZMod q) {Y : ℕ} (hY : 3 ≤ Y) (M : ℕ) :
    ∑ n ∈ Ioc Y M with ((n : ℕ) : ZMod q) = a, Λ n / n ≤
      #{p ∈ Ioc Y M | p.Prime ∧ ((p : ℕ) : ZMod q) = a} * (Real.log Y / Y) +
        (Real.log (Nat.sqrt Y) + 2 + 2 * Real.log 4) / Nat.sqrt Y := by
  rw [← sum_filter_add_sum_filter_not _ Nat.Prime, filter_filter, filter_filter]
  have hY' : (3 : ℝ) ≤ Y := by exact_mod_cast hY
  gcongr
  · have hfilt : ({p ∈ Ioc Y M | ((p : ℕ) : ZMod q) = a ∧ p.Prime} : Finset ℕ) =
        {p ∈ Ioc Y M | p.Prime ∧ ((p : ℕ) : ZMod q) = a} := filter_congr fun _ _ ↦ and_comm
    rw [hfilt, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun p hp ↦ ?_
    simp only [mem_filter, mem_Ioc] at hp
    rw [vonMangoldt_apply_prime hp.2.1]
    exact log_div_self_le_of_three_le hY' (by exact_mod_cast hp.1.1.le)
  · calc ∑ n ∈ Ioc Y M with ((n : ℕ) : ZMod q) = a ∧ ¬ n.Prime, Λ n / n
          ≤ ∑ n ∈ Ioc Y M with ¬ n.Prime, Λ n / n := by
            refine sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦
              div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
            intro n hn
            simp only [mem_filter] at hn ⊢
            exact ⟨hn.1, hn.2.2⟩
      _ ≤ _ := sum_Ioc_nonprime_vonMangoldt_div_le (by omega) M

/-- **Lower bound for the class sum.** For `a` coprime to `q`, `1 ≤ y ≤ x`, and `‖S_χ‖ ≤ B` on
`[1, ∞)` for every `χ ≠ 1`:
`S_a(x) − S_a(y) ≥ (log(x/y) − 2C₀ − log q − 2B(φ(q) − 1))/φ(q)` with `C₀ = 3`. -/
theorem classSum_sub_ge [NeZero q] {a : ZMod q} (ha : IsUnit a) {B : ℝ}
    (hS : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ x : ℝ, 1 ≤ x → ‖twistedSum χ x‖ ≤ B)
    {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    (q.totient : ℝ)⁻¹ * (Real.log (x / y) - 2 * 3 - Real.log q - 2 * B * (q.totient - 1)) ≤
      classSum a x - classSum a y := by
  rw [classSum_sub_eq ha]
  gcongr
  rw [Complex.re_sum, ← add_sum_erase _ _ (mem_univ 1)]
  have h1 : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
    rw [dirichletCharacter_apply_inv_of_isUnit _ ha, MulChar.one_apply ha, inv_one]
  rw [h1, one_mul]
  have hcard : (univ.erase (1 : DirichletCharacter ℂ q)).card = q.totient - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hφ : 1 ≤ q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hrest : -(2 * B * (q.totient - 1)) ≤
      ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
        (χ a⁻¹ * (twistedSum χ x - twistedSum χ y)).re := by
    have : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), (-(2 * B)) =
        -(2 * B * (q.totient - 1)) := by
      rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_sub hφ]; push_cast; ring
    rw [← this]
    refine sum_le_sum fun χ hχ ↦ ?_
    have hχ1 : χ ≠ 1 := ne_of_mem_erase hχ
    have hn : ‖χ a⁻¹ * (twistedSum χ x - twistedSum χ y)‖ ≤ 2 * B := by
      rw [norm_mul]
      calc ‖χ a⁻¹‖ * ‖twistedSum χ x - twistedSum χ y‖ ≤ 1 * (B + B) := by
            gcongr
            · exact DirichletCharacter.norm_le_one χ _
            · exact (norm_sub_le _ _).trans
                (add_le_add (hS χ hχ1 x (hy.trans hyx)) (hS χ hχ1 y hy))
        _ = 2 * B := by ring
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
    linarith
  have hmain := log_div_sub_le_re_twistedSum_one_sub (q := q) hy hyx
  linarith

/-- **Twenty-two primes in a progression.** Let `q ≥ 3`, `a` coprime to `q`, and `B ≥ 1` with
`‖S_χ(x)‖ ≤ B` for every Dirichlet character `χ ≠ 1` mod `q` and every `x ≥ 1`. Then at least
22 primes `p ≡ a (mod q)` satisfy `q^8 < p ≤ q^8 · exp(5qB)`. -/
theorem twentytwo_primes_of_twisted_bound (hq : 3 ≤ q) {a : ℕ} (ha : a.Coprime q) {B : ℝ}
    (hB : 1 ≤ B)
    (hS : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ x : ℝ, 1 ≤ x → ‖twistedSum χ x‖ ≤ B) :
    22 ≤ #{p ∈ Ioc (q ^ 8) ⌊(q : ℝ) ^ 8 * Real.exp (5 * q * B)⌋₊ |
      p.Prime ∧ p ≡ a [MOD q]} := by
  have : NeZero q := ⟨by omega⟩
  have ua : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  set Y : ℕ := q ^ 8 with hYdef
  set x : ℝ := (q : ℝ) ^ 8 * Real.exp (5 * q * B) with hxdef
  have hYc : (Y : ℝ) = (q : ℝ) ^ 8 := by rw [hYdef]; push_cast; rfl
  have hq4 : 81 ≤ q ^ 4 := (Nat.pow_le_pow_left hq 4).trans' (by norm_num)
  have hY6561 : 6561 ≤ Y := by
    rw [hYdef]; exact (Nat.pow_le_pow_left hq 8).trans' (by norm_num)
  have hY' : (6561 : ℝ) ≤ Y := by exact_mod_cast hY6561
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hYx : (Y : ℝ) ≤ x := by
    rw [hxdef, hYc]
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
  have hlogxy : Real.log (x / Y) = 5 * q * B := by
    rw [hxdef, hYc, mul_div_cancel_left₀ _ (by positivity), Real.log_exp]
  -- the lower bound `S_a(x) − S_a(Y) ≥ 1`
  have hlow : 1 ≤ classSum (a : ZMod q) x - classSum (a : ZMod q) Y := by
    refine le_trans ?_ (classSum_sub_ge ua hS (by linarith) hYx)
    rw [hlogxy]
    set φ : ℝ := (q.totient : ℝ) with hφdef
    have hφpos : 0 < φ := by
      rw [hφdef]; exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hφq : φ ≤ q := by rw [hφdef]; exact_mod_cast Nat.totient_le q
    have hlogq : Real.log q ≤ q - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [le_inv_mul_iff₀ hφpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hφq) (by linarith : (0 : ℝ) ≤ 2 * B + 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * q + 2) (sub_nonneg.mpr hB)]
  -- the upper bound by the number of primes
  have hup := sum_Ioc_classSum_le (a : ZMod q) (by omega : 3 ≤ Y) ⌊x⌋₊
  rw [← classSum_sub_classSum_nat _ hYx] at hup
  have hcard : #{p ∈ Ioc Y ⌊x⌋₊ | p.Prime ∧ ((p : ℕ) : ZMod q) = (a : ZMod q)} =
      #{p ∈ Ioc (q ^ 8) ⌊(q : ℝ) ^ 8 * Real.exp (5 * q * B)⌋₊ | p.Prime ∧ p ≡ a [MOD q]} := by
    congr 1
    exact filter_congr fun p _ ↦ by rw [ZMod.natCast_eq_natCast_iff]
  rw [hcard] at hup
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num); linarith
  have hlogY : Real.log Y / Y ≤ 16 / 6561 := by
    have h1 := log_div_self_le_of_three_le (by norm_num) hY'
    have h3 : Real.log 6561 ≤ 16 := by
      rw [show (6561 : ℝ) = 3 ^ 8 by norm_num, Real.log_pow]; push_cast; linarith
    calc Real.log Y / Y ≤ Real.log 6561 / 6561 := h1
      _ ≤ 16 / 6561 := by gcongr
  -- the prime-power term: `s = ⌊√(q^8)⌋ = q^4 ≥ 81`
  have hs : Nat.sqrt Y = q ^ 4 := by
    rw [hYdef, show q ^ 8 = (q ^ 4) ^ 2 by ring, Nat.sqrt_eq']
  have hE : (Real.log (Nat.sqrt Y) + 2 + 2 * Real.log 4) / Nat.sqrt Y ≤ 16 / 81 := by
    rw [hs]
    have hs81 : (81 : ℝ) ≤ ((q ^ 4 : ℕ) : ℝ) := by exact_mod_cast hq4
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (x := 4) (by norm_num); linarith
    have h1 := log_div_self_le_of_three_le (by norm_num) hs81
    have h81 : Real.log 81 ≤ 8 := by
      rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
    have h2 : (2 + 2 * Real.log 4) / ((q ^ 4 : ℕ) : ℝ) ≤ 8 / 81 := by
      calc (2 + 2 * Real.log 4) / ((q ^ 4 : ℕ) : ℝ) ≤ 8 / ((q ^ 4 : ℕ) : ℝ) := by
            gcongr; linarith
        _ ≤ 8 / 81 := by gcongr
    rw [add_assoc, add_div]
    have : Real.log ((q ^ 4 : ℕ) : ℝ) / ((q ^ 4 : ℕ) : ℝ) ≤ 8 / 81 :=
      h1.trans (by gcongr)
    linarith
  by_contra hlt
  push Not at hlt
  have hle : (#{p ∈ Ioc Y ⌊x⌋₊ | p.Prime ∧ p ≡ a [MOD q]} : ℝ) ≤ 21 := by
    exact_mod_cast Nat.lt_succ_iff.mp hlt
  have hnn : 0 ≤ Real.log Y / Y := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ Y)
    positivity
  nlinarith

end ZInQ.Progressions
