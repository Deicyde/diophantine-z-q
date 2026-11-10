import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The window lemma

Step 1 of `docs/research/gt-dense.md`. A set `A` whose counting function is at least `c π(N)` for
infinitely many `N` has, for infinitely many `Z`, at least `c₁ Z / log Z` elements in the dyadic
window `(Z/2, Z]`, with `c₁ = c log 2 / 24`.

Proof: cut `[0, N]` into the windows `(N/2^{j+1}, N/2^j]` for `j < J = log₂ ⌊√N⌋` and the tail
`[0, N/2^J]`, which has `O(√N)` elements. Every window has `Z_j = N/2^j ≥ ⌊√N⌋`, so
`log Z_j ≥ log N / 3`. If every window had fewer than `c₁ Z_j / log Z_j` elements of `A`, the windows
would hold fewer than `6 c₁ N / log N = (c log 2 / 4) N / log N` elements together. Chebyshev's
lower bound `π(N) ≥ (N log 2 − log (N+1)) / log N` (Mathlib's `Chebyshev.pi_ge`) then contradicts
`c π(N) ≤ |A ∩ [0, N]|` for large `N`. Only the lower bound for `π` is needed; the tail is bounded
trivially.

This file imports only Mathlib. The density hypothesis appears unfolded, in the shape of the body of
`ZInQ.PrimesRelUpperDensityPos`; the bridge applies it.
-/

namespace ZInQ.GreenTaoDense

open Filter Finset Real Asymptotics

/-- Splitting `[0, b]` at `a ≤ b`. -/
theorem card_filter_range_le_add_Ioc (A : Set ℕ) [DecidablePred (· ∈ A)] {a b : ℕ} (_hab : a ≤ b) :
    ((range (b + 1)).filter (· ∈ A)).card ≤
      ((range (a + 1)).filter (· ∈ A)).card + ((Ioc a b).filter (· ∈ A)).card := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro x hx
  simp only [mem_filter, mem_range, mem_union, mem_Ioc] at hx ⊢
  by_cases h : x ≤ a
  · exact Or.inl ⟨by omega, hx.2⟩
  · exact Or.inr ⟨⟨by omega, by omega⟩, hx.2⟩

/-- Dyadic decomposition of `[0, N]`. -/
theorem card_filter_range_le_sum_windows (A : Set ℕ) [DecidablePred (· ∈ A)] (N J : ℕ) :
    ((range (N + 1)).filter (· ∈ A)).card ≤
      ((range (N / 2 ^ J + 1)).filter (· ∈ A)).card +
        ∑ j ∈ range J, ((Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j)).filter (· ∈ A)).card := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hdiv : N / 2 ^ (J + 1) = N / 2 ^ J / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have h := card_filter_range_le_add_Ioc A (Nat.div_le_self (N / 2 ^ J) 2)
    rw [← hdiv] at h
    rw [sum_range_succ]
    omega

/-- `√x · log x = o(x)`. -/
theorem isLittleO_sqrt_mul_log : (fun x : ℝ => √x * log x) =o[atTop] id := by
  have h := (isBigO_refl (fun x : ℝ => x ^ (1 / (2 : ℝ))) atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  refine (h.congr' ?_ ?_)
  · filter_upwards with x
    rw [sqrt_eq_rpow]
  · filter_upwards [eventually_ge_atTop 0] with x hx
    rw [← sqrt_eq_rpow, mul_self_sqrt hx, id]

/-- The error terms of the window lemma are eventually small. -/
theorem eventually_window_error (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, (2 * √(N : ℝ) + 2) * log N + c * log ((N : ℝ) + 1) <
      3 / 4 * (c * log 2) * N ∨ c ≤ 0 := by
  rcases le_or_gt c 0 with hc | hc
  · exact Eventually.of_forall fun _ => Or.inr hc
  have hε : 0 < c * log 2 / 2 := by have := log_pos one_lt_two; positivity
  have hO : (fun x : ℝ => 2 * (√x * log x) + (2 + c) * log x + c * log 2) =o[atTop] id :=
    ((isLittleO_sqrt_mul_log.const_mul_left 2).add
      (isLittleO_log_id_atTop.const_mul_left (2 + c))).add (isLittleO_const_id_atTop _)
  have hev := (hO.def hε).and (eventually_ge_atTop (1 : ℝ))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev] with N ⟨hN, hN1⟩
  left
  have hlogN : 0 ≤ log (N : ℝ) := log_nonneg hN1
  have hsq : 0 ≤ √(N : ℝ) * log N := by positivity
  have hlog2 : 0 < log (2 : ℝ) := log_pos one_lt_two
  have hl1 : log ((N : ℝ) + 1) ≤ log 2 + log N := by
    rw [← log_mul (by norm_num) (by linarith)]
    exact log_le_log (by linarith) (by linarith)
  rw [id, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)] at hN
  have hNpos : (0 : ℝ) < N := by linarith
  have : c * log ((N : ℝ) + 1) ≤ c * log 2 + c * log N := by nlinarith
  nlinarith

/-- **The window lemma** (with the density hypothesis unfolded). -/
theorem frequently_window_of {A : Set ℕ} [DecidablePred (· ∈ A)] {c : ℝ} (hc : 0 < c)
    (h : ∃ᶠ N in atTop, c * (Nat.primeCounting N : ℝ) ≤
      (((range (N + 1)).filter (· ∈ A)).card : ℝ)) :
    ∃ᶠ Z : ℕ in atTop, c * Real.log 2 / 24 * Z / Real.log Z ≤
      (((Ioc (Z / 2) Z).filter (· ∈ A)).card : ℝ) := by
  set ε : ℝ := c * Real.log 2 / 24 with hεdef
  have hlog2 : 0 < Real.log 2 := log_pos one_lt_two
  have hε : 0 < ε := by positivity
  rw [frequently_atTop]
  intro Z₀
  have hev : ∀ᶠ N : ℕ in atTop, ((2 * √(N : ℝ) + 2) * log N + c * log ((N : ℝ) + 1) <
      3 / 4 * (c * log 2) * N ∨ c ≤ 0) ∧ (Z₀ + 3) ^ 2 ≤ N :=
    (eventually_window_error c).and (eventually_ge_atTop _)
  obtain ⟨N, hcount, herr, hN⟩ := (h.and_eventually hev).exists
  replace herr := herr.resolve_right (not_le.2 hc)
  set s := Nat.sqrt N with hs
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have hs3 : Z₀ + 3 ≤ s := Nat.le_sqrt'.2 hN
  have hs0 : s ≠ 0 := by omega
  set J := Nat.log 2 s with hJ
  have h2J : 2 ^ J ≤ s := Nat.pow_log_le_self 2 hs0
  have h2J' : s < 2 * 2 ^ J := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) s
    rw [← hJ, pow_succ] at this; omega
  -- each window is large
  have hZj : ∀ j ≤ J, s ≤ N / 2 ^ j := by
    intro j hj
    have hj2 : 2 ^ j ≤ s := (Nat.pow_le_pow_right (by norm_num) hj).trans h2J
    rw [Nat.le_div_iff_mul_le (by positivity)]
    exact (Nat.mul_le_mul_left s hj2).trans hsN
  have hNpos : 0 < N := by nlinarith
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by nlinarith)
  have hlogN : 0 < Real.log N := log_pos hNR
  by_contra hcon
  push Not at hcon
  have hbad : ∀ j < J, (((Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j)).filter (· ∈ A)).card : ℝ) ≤
      3 * ε * N / Real.log N * (1 / 2) ^ j := by
    intro j hj
    set Z := N / 2 ^ j with hZ
    have hZs := hZj j hj.le
    have hZ2 : N / 2 ^ (j + 1) = Z / 2 := by rw [hZ, pow_succ, Nat.div_div_eq_div_mul]
    have hlt := hcon Z (by omega)
    rw [← hZ2] at hlt
    have hZ1 : (1 : ℝ) < Z := by exact_mod_cast (show 1 < Z by omega)
    have hlogZ : 0 < Real.log Z := log_pos hZ1
    -- `log N ≤ 3 log Z`
    have hN3 : N ≤ Z ^ 3 := by
      have : (s + 1) * (s + 1) ≤ s ^ 3 := by nlinarith
      calc N ≤ s ^ 3 := by omega
        _ ≤ Z ^ 3 := Nat.pow_le_pow_left hZs 3
    have hlog3 : Real.log N ≤ 3 * Real.log Z := by
      have e := Real.log_pow (Z : ℝ) 3
      push_cast at e
      rw [← e]
      exact log_le_log (by positivity) (by exact_mod_cast hN3)
    have hZle : (Z : ℝ) ≤ N / 2 ^ j := by
      rw [hZ]; exact_mod_cast (Nat.cast_div_le (α := ℝ))
    calc (((Ioc (N / 2 ^ (j + 1)) Z).filter (· ∈ A)).card : ℝ) ≤ ε * Z / Real.log Z := hlt.le
      _ ≤ 3 * ε * Z / Real.log N := by
        rw [div_le_div_iff₀ hlogZ hlogN]
        nlinarith [mul_le_mul_of_nonneg_left hlog3 (by positivity : 0 ≤ ε * Z)]
      _ ≤ 3 * ε * (N / 2 ^ j) / Real.log N := by gcongr
      _ = 3 * ε * N / Real.log N * (1 / 2) ^ j := by
        rw [one_div_pow]; field_simp
  -- the tail
  have htail : N / 2 ^ J + 1 ≤ 2 * s + 2 := by
    have h1 := Nat.div_mul_le_self N (2 ^ J)
    have h2 : N / 2 ^ J * 2 ^ J < (2 * (s + 1)) * 2 ^ J := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right h2
    omega
  have hdec := card_filter_range_le_sum_windows A N J
  have htail' : (((range (N / 2 ^ J + 1)).filter (· ∈ A)).card : ℝ) ≤ 2 * √(N : ℝ) + 2 := by
    have h1 : ((range (N / 2 ^ J + 1)).filter (· ∈ A)).card ≤ 2 * s + 2 :=
      (card_filter_le _ _).trans (by rw [card_range]; exact htail)
    have h2 : (s : ℝ) ≤ √(N : ℝ) := Real.nat_sqrt_le_real_sqrt
    calc _ ≤ ((2 * s + 2 : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := by push_cast; linarith
  have hsum : (∑ j ∈ range J, (((Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j)).filter (· ∈ A)).card : ℝ)) ≤
      6 * ε * N / Real.log N := by
    calc _ ≤ ∑ j ∈ range J, 3 * ε * N / Real.log N * (1 / 2 : ℝ) ^ j :=
          sum_le_sum fun j hj => hbad j (mem_range.1 hj)
      _ = 3 * ε * N / Real.log N * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j := by rw [mul_sum]
      _ ≤ 3 * ε * N / Real.log N * 2 := by
          gcongr; exact sum_geometric_two_le J
      _ = _ := by ring
  have hupper : (((range (N + 1)).filter (· ∈ A)).card : ℝ) ≤
      2 * √(N : ℝ) + 2 + 6 * ε * N / Real.log N := by
    have : (((range (N + 1)).filter (· ∈ A)).card : ℝ) ≤
        (((range (N / 2 ^ J + 1)).filter (· ∈ A)).card : ℝ) +
          ∑ j ∈ range J, (((Ioc (N / 2 ^ (j + 1)) (N / 2 ^ j)).filter (· ∈ A)).card : ℝ) := by
      exact_mod_cast hdec
    linarith
  have hpi := Chebyshev.pi_ge N
  have hlower : c * ((N * Real.log 2 - Real.log (N + 1)) / Real.log N) ≤
      2 * √(N : ℝ) + 2 + 6 * ε * N / Real.log N :=
    ((mul_le_mul_of_nonneg_left hpi hc.le).trans hcount).trans hupper
  have hmul : c * (N * Real.log 2 - Real.log (N + 1)) ≤
      (2 * √(N : ℝ) + 2) * Real.log N + 6 * ε * N := by
    have e1 : c * ((N * Real.log 2 - Real.log (N + 1)) / Real.log N) * Real.log N =
        c * (N * Real.log 2 - Real.log (N + 1)) := by field_simp
    have e2 : (2 * √(N : ℝ) + 2 + 6 * ε * N / Real.log N) * Real.log N =
        (2 * √(N : ℝ) + 2) * Real.log N + 6 * ε * N := by field_simp
    rw [← e1, ← e2]
    exact mul_le_mul_of_nonneg_right hlower hlogN.le
  rw [hεdef] at hmul
  nlinarith

end ZInQ.GreenTaoDense
