import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Lane RC1-boolean, part 4: the convolution estimate (5.11)

Proof of Proposition `ex:limits-coefficient-transfer` (`diophantine_zq.tex` 5647–5739), tex
5694–5726, at the nonzero address `x` produced by the Boolean argument.

**Representation of `𝒪`.** `Λ = ℤ₂[[t]]` and `𝒪 = (Λ_{(2)})^∧` (Definition `ex:arith-data`, tex
2747–2748). The completed local ring `𝒪` is the ring of Laurent series `Σ_{i ∈ ℤ} a_i t^i` with
`a_i ∈ ℤ₂` and `a_i → 0` as `i → −∞`, its valuation is the Gauss valuation `min_i v₂(a_i)`, and
`𝒪[1/2]` is its fraction field. We do not build this ring: an element of `𝒪` enters only through
its Laurent coefficients `ℤ → ℤ₂`, an element of `Λ[1/2]` through its power-series coefficients
`ℕ → ℚ₂` with bounded denominators (`InLambdaHalf`), and the identity `f_x ũ_x = d_x` of (5.9)
through the convolution of coefficients that defines the product of Laurent series:
`[t^n] d_x = Σ_{k ≥ 0} [t^{n−k}] f_x · [t^k] ũ_x` (a convergent sum in `ℚ₂`).

Main results (kind PROVED):
* `gauss_lower_bound` (tex 5697–5700): `v_𝒪(f_x) ≤ c` and the integrality of `d_x = f_x ũ_x`
  give `v_𝒪(ũ_x) ≥ −c`;
* `base_constant_term`, `base_lower_bound` (tex 5703–5709): `[t^0] d_0 = f_0(0) ũ_0(0)` and
  `v₂ ũ_0(0) ≥ −c`;
* `convolution_estimate` (tex 5710–5718): `[t^0] d_x = F_x ũ_x(0) + E_x` with
  `E_x = Σ_{i<0} [t^i] f_x [t^{−i}] ũ_x` and `v₂(E_x) ≥ M − c`;
* `difference_estimate` (tex 5719–5726): (5.11) `v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c`.
Valuations are written through the `2`-adic norm: `v₂(z) ≥ m ⟺ ‖z‖ ≤ 2^{−m}`.
-/

namespace ZInQ.Manuscript.RC.Boolean

/-- `Λ[1/2] ⊂ ℚ₂[[t]]`, `Λ = ℤ₂[[t]]`: the power series `Σ_n u_n t^n` with `u_n = g_n / 2^e` for one
`e ∈ ℕ` and `g_n ∈ ℤ₂` ("`ũ_x ∈ Λ[1/2]`", tex 5703–5704). -/
def InLambdaHalf (u : ℕ → ℚ_[2]) : Prop :=
  ∃ (e : ℕ) (g : ℕ → ℤ_[2]), ∀ n, u n = (g n : ℚ_[2]) / 2 ^ e

/-- `Λ[1/2]` by bounded denominators: a power series with `‖u_n‖ ≤ 2^e` for all `n` lies in
`Λ[1/2]` (take `g_n = 2^e u_n ∈ ℤ₂`). -/
theorem inLambdaHalf_of_norm_le {u : ℕ → ℚ_[2]} {e : ℕ} (h : ∀ n, ‖u n‖ ≤ (2 : ℝ) ^ e) :
    InLambdaHalf u := by
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := Padic.norm_p (p := 2)
    push_cast at this
    exact this
  have hg : ∀ n, ‖(2 : ℚ_[2]) ^ e * u n‖ ≤ 1 := by
    intro n
    rw [norm_mul, norm_pow, h2, inv_pow]
    calc ((2 : ℝ) ^ e)⁻¹ * ‖u n‖ ≤ ((2 : ℝ) ^ e)⁻¹ * (2 : ℝ) ^ e :=
          mul_le_mul_of_nonneg_left (h n) (inv_nonneg.mpr (pow_pos two_pos e).le)
      _ = 1 := inv_mul_cancel₀ (pow_pos two_pos e).ne'
  refine ⟨e, fun n => ⟨(2 : ℚ_[2]) ^ e * u n, hg n⟩, fun n => ?_⟩
  have h2e : (2 : ℚ_[2]) ^ e ≠ 0 := pow_ne_zero e two_ne_zero
  change u n = (2 : ℚ_[2]) ^ e * u n / 2 ^ e
  rw [mul_div_assoc, mul_div_cancel₀ _ h2e]

/-! ### Auxiliary facts about the `2`-adic norm -/

/-- Divisibility by `2^m` in `ℤ₂` bounds the norm by `2^{-m}`. -/
lemma norm_le_two_zpow_of_dvd {z : ℤ_[2]} {m : ℕ} (h : (2 : ℤ_[2]) ^ m ∣ z) :
    ‖z‖ ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
  have := (PadicInt.norm_le_pow_iff_mem_span_pow z m).mpr
    (Ideal.mem_span_singleton.mpr (by simpa using h))
  exact_mod_cast this

/-- Divisibility by `2^m` in `ℤ₂` bounds the norm of the image in `ℚ₂` by `2^{-m}`. -/
lemma norm_coe_le_two_zpow_of_dvd {z : ℤ_[2]} {m : ℕ} (h : (2 : ℤ_[2]) ^ m ∣ z) :
    ‖(z : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
  rw [PadicInt.norm_coe]; exact norm_le_two_zpow_of_dvd h

/-- A nonzero `2`-adic integer of valuation `c` has norm `2^{-c}`. -/
lemma norm_eq_two_zpow_neg_of_valuation {z : ℤ_[2]} {c : ℕ} (hz : z ≠ 0)
    (hc : z.valuation = c) : ‖z‖ = (2 : ℝ) ^ (-(c : ℤ)) := by
  rw [PadicInt.norm_eq_zpow_neg_valuation hz, hc]; norm_num

/-- Discreteness of the norm of `ℚ₂`: a norm below `2^{n+1}` is at most `2^n`. -/
lemma padic_norm_le_two_zpow_of_lt {x : ℚ_[2]} {n : ℤ} (h : ‖x‖ < (2 : ℝ) ^ (n + 1)) :
    ‖x‖ ≤ (2 : ℝ) ^ n := by
  have := Padic.norm_le_pow_iff_norm_lt_pow_add_one x n
  push_cast at this
  exact this.mpr h

/-- Discreteness of the norm of `ℤ₂`: a norm below `2^{n+1}` is at most `2^n`. -/
lemma padicInt_norm_le_two_zpow_of_lt {x : ℤ_[2]} {n : ℤ} (h : ‖x‖ < (2 : ℝ) ^ (n + 1)) :
    ‖x‖ ≤ (2 : ℝ) ^ n := by
  rw [← PadicInt.norm_coe] at h ⊢; exact padic_norm_le_two_zpow_of_lt h

/-- The ultrametric inequality for a difference in `ℚ₂`. -/
lemma padic_norm_sub_le_of_le {x y : ℚ_[2]} {C : ℝ} (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) :
    ‖x - y‖ ≤ C := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rwa [norm_neg]))

/-- Ultrametric isolation of one term: if every other term of a convergent sum in `ℚ₂` has norm
at most `C < ‖f k₀‖`, then the sum has norm at least `‖f k₀‖`. -/
lemma norm_le_norm_of_hasSum_of_isolated {f : ℕ → ℚ_[2]} {s : ℚ_[2]} (hf : HasSum f s)
    (k₀ : ℕ) {C : ℝ} (hC : ∀ k, k ≠ k₀ → ‖f k‖ ≤ C) (hlt : C < ‖f k₀‖) : ‖f k₀‖ ≤ ‖s‖ := by
  classical
  have h1 := hf.update k₀ 0
  have h2 : ‖0 - f k₀ + s‖ ≤ C := by
    rw [← h1.tsum_eq]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
    by_cases hk : k = k₀
    · rw [hk, Function.update_self, norm_zero]
      exact (norm_nonneg _).trans (hC (k₀ + 1) (by omega))
    · rw [Function.update_of_ne hk]
      exact hC k hk
  have h4 : ‖f k₀‖ ≤ max ‖s‖ ‖0 - f k₀ + s‖ := by
    calc ‖f k₀‖ = ‖s + -(0 - f k₀ + s)‖ := by congr 1; ring
      _ ≤ max ‖s‖ ‖-(0 - f k₀ + s)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖s‖ ‖0 - f k₀ + s‖ := by rw [norm_neg]
  rcases le_max_iff.mp h4 with h | h
  · exact h
  · exact absurd (h.trans h2) (not_le.mpr hlt)

/-- **Gauss step** (tex 5697–5700; kind PROVED). Let `F = ([t^i] f_x)_{i ∈ ℤ}`, `U = ([t^n] ũ_x)`
with `ũ_x ∈ Λ[1/2]`, and `D = ([t^n] d_x)` integral, with `f_x ũ_x = d_x` coefficientwise. If the
constant coefficient `F_0` has valuation `c` and every negative coefficient has valuation `> c`
(so `v_𝒪(f_x) ≤ c` is attained in nonnegative degree; positive coefficients may have smaller
valuation), then `v_𝒪(ũ_x) ≥ −c`, i.e. `‖[t^n] ũ_x‖ ≤ 2^c` for every `n`. -/
theorem gauss_lower_bound {F : ℤ → ℤ_[2]} {U : ℕ → ℚ_[2]} {D : ℤ → ℤ_[2]} {c : ℕ}
    (hU : InLambdaHalf U)
    (hconv : ∀ n : ℤ, HasSum (fun k : ℕ => (F (n - k) : ℚ_[2]) * U k) (D n))
    (hF0 : F 0 ≠ 0) (hc : (F 0).valuation = c)
    (hneg : ∀ i < 0, (2 : ℤ_[2]) ^ (c + 1) ∣ F i) :
    ∀ n, ‖U n‖ ≤ (2 : ℝ) ^ c := by
  classical
  obtain ⟨e, g, hg⟩ := hU
  have two_zpow_pos : ∀ m : ℤ, (0 : ℝ) < (2 : ℝ) ^ m := fun m => zpow_pos two_pos m
  -- every coefficient of `U` has norm at most `2^e`
  have hUe : ∀ k, ‖U k‖ ≤ (2 : ℝ) ^ (e : ℤ) := by
    intro k
    have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
      have := Padic.norm_p (p := 2)
      push_cast at this
      exact this
    rw [hg k, norm_div, norm_pow, h2, PadicInt.norm_coe, inv_pow, div_inv_eq_mul, zpow_natCast]
    calc ‖g k‖ * 2 ^ e ≤ 1 * 2 ^ e :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (pow_pos two_pos _).le
      _ = 2 ^ e := one_mul _
  -- argue by contradiction from one coefficient of norm `> 2^c`
  intro n₁
  refine le_of_not_gt fun hn₁ => ?_
  rw [← zpow_natCast] at hn₁
  -- the largest norm `μ = 2^{e - j₀}` of a coefficient of `U`, first attained at `k₀`
  have hce : c ≤ e := by
    have := (zpow_lt_zpow_iff_right₀ (one_lt_two : (1 : ℝ) < 2)).mp (hn₁.trans_le (hUe n₁))
    omega
  have hP : ∃ j : ℕ, ∃ k, (2 : ℝ) ^ ((e : ℤ) - j) ≤ ‖U k‖ :=
    ⟨e - c, n₁, by rw [show (e : ℤ) - ((e - c : ℕ) : ℤ) = c by omega]; exact hn₁.le⟩
  set j₀ := Nat.find hP with hj₀
  set μ : ℝ := (2 : ℝ) ^ ((e : ℤ) - j₀) with hμ
  have hμpos : 0 < μ := two_zpow_pos _
  have hμmax : ∀ k, ‖U k‖ ≤ μ := by
    intro k
    refine le_of_not_gt fun hk => ?_
    have h1 : (2 : ℝ) ^ ((e : ℤ) - j₀ + 1) ≤ ‖U k‖ :=
      le_of_not_gt fun h => absurd (padic_norm_le_two_zpow_of_lt h) (not_le.mpr hk)
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · have h3 : (2 : ℝ) ^ (e : ℤ) < (2 : ℝ) ^ ((e : ℤ) - j₀ + 1) :=
        zpow_lt_zpow_right₀ one_lt_two (by omega)
      exact absurd (h1.trans (hUe k)) (not_le.mpr h3)
    · refine Nat.find_min hP (show j₀ - 1 < j₀ by omega) ⟨k, ?_⟩
      rw [show (e : ℤ) - ((j₀ - 1 : ℕ) : ℤ) = (e : ℤ) - j₀ + 1 by omega]
      exact h1
  have hμc : (2 : ℝ) ^ (c : ℤ) < μ := hn₁.trans_le (hμmax n₁)
  have hμspec : ∃ k, μ ≤ ‖U k‖ := Nat.find_spec hP
  set k₀ := Nat.find hμspec with hk₀
  have hUk₀ : ‖U k₀‖ = μ := le_antisymm (hμmax k₀) (Nat.find_spec hμspec)
  have hUlt : ∀ k, k < k₀ → ‖U k‖ < μ := fun k hk => not_le.mp (Nat.find_min hμspec hk)
  -- the largest norm `ν = 2^{-j₁}` of a coefficient of `F` in nonnegative degree, first
  -- attained at `i₀`
  have hF0n : ‖F ((0 : ℕ) : ℤ)‖ = (2 : ℝ) ^ (-(c : ℤ)) := by
    rw [Nat.cast_zero]; exact norm_eq_two_zpow_neg_of_valuation hF0 hc
  have hQ : ∃ j : ℕ, ∃ i : ℕ, (2 : ℝ) ^ (-(j : ℤ)) ≤ ‖F i‖ := ⟨c, 0, hF0n.ge⟩
  set j₁ := Nat.find hQ with hj₁
  set ν : ℝ := (2 : ℝ) ^ (-(j₁ : ℤ)) with hν
  have hνpos : 0 < ν := two_zpow_pos _
  have hνmax : ∀ i : ℕ, ‖F i‖ ≤ ν := by
    intro i
    refine le_of_not_gt fun hi => ?_
    have h1 : (2 : ℝ) ^ (-(j₁ : ℤ) + 1) ≤ ‖F i‖ :=
      le_of_not_gt fun h => absurd (padicInt_norm_le_two_zpow_of_lt h) (not_le.mpr hi)
    rcases Nat.eq_zero_or_pos j₁ with h0 | hpos
    · have h3 : (2 : ℝ) ^ (0 : ℤ) < (2 : ℝ) ^ (-(j₁ : ℤ) + 1) :=
        zpow_lt_zpow_right₀ one_lt_two (by omega)
      rw [zpow_zero] at h3
      exact absurd (h1.trans (PadicInt.norm_le_one _)) (not_le.mpr h3)
    · refine Nat.find_min hQ (show j₁ - 1 < j₁ by omega) ⟨i, ?_⟩
      rw [show -((j₁ - 1 : ℕ) : ℤ) = -(j₁ : ℤ) + 1 by omega]
      exact h1
  have hνc : (2 : ℝ) ^ (-(c : ℤ)) ≤ ν :=
    zpow_le_zpow_right₀ one_le_two (by have := Nat.find_min' hQ ⟨0, hF0n.ge⟩; omega)
  have hνspec : ∃ i : ℕ, ν ≤ ‖F i‖ := Nat.find_spec hQ
  set i₀ := Nat.find hνspec with hi₀
  have hFi₀ : ‖F i₀‖ = ν := le_antisymm (hνmax i₀) (Nat.find_spec hνspec)
  -- negative coefficients of `F` have norm `≤ 2^{-c-1} < ν`
  have hFneg : ∀ i : ℤ, i < 0 → ‖F i‖ < ν := by
    intro i hi
    refine lt_of_le_of_lt (norm_le_two_zpow_of_dvd (hneg i hi)) (lt_of_lt_of_le ?_ hνc)
    exact zpow_lt_zpow_right₀ one_lt_two (by omega)
  have hFle : ∀ i : ℤ, ‖F i‖ ≤ ν := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · exact (hFneg i hi).le
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      exact hνmax m
  have hFlt : ∀ i : ℤ, i < i₀ → ‖F i‖ < ν := by
    intro i hi
    rcases lt_or_ge i 0 with hi' | hi'
    · exact hFneg i hi'
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi'
      exact not_le.mp (Nat.find_min hνspec (by omega))
  -- in `[t^{i₀ + k₀}] d` the term `k = k₀` has norm `νμ` and every other term is smaller
  set n : ℤ := (i₀ : ℤ) + k₀ with hn
  have hνμ : ν * μ = (2 : ℝ) ^ ((e : ℤ) - j₀ - j₁) := by
    rw [hν, hμ, ← zpow_add₀ two_ne_zero]; congr 1; ring
  have hterm₀ : ‖(F (n - k₀) : ℚ_[2]) * U k₀‖ = ν * μ := by
    rw [norm_mul, PadicInt.norm_coe, show n - (k₀ : ℤ) = i₀ by omega, hFi₀, hUk₀]
  have hterm : ∀ k, k ≠ k₀ →
      ‖(F (n - k) : ℚ_[2]) * U k‖ ≤ (2 : ℝ) ^ ((e : ℤ) - j₀ - j₁ - 1) := by
    intro k hk
    apply padic_norm_le_two_zpow_of_lt
    rw [sub_add_cancel, ← hνμ, norm_mul, PadicInt.norm_coe]
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · calc ‖F (n - k)‖ * ‖U k‖ ≤ ν * ‖U k‖ :=
            mul_le_mul_of_nonneg_right (hFle _) (norm_nonneg _)
        _ < ν * μ := mul_lt_mul_of_pos_left (hUlt k hlt) hνpos
    · calc ‖F (n - k)‖ * ‖U k‖ ≤ ‖F (n - k)‖ * μ :=
            mul_le_mul_of_nonneg_left (hμmax k) (norm_nonneg _)
        _ < ν * μ := mul_lt_mul_of_pos_right (hFlt _ (by omega)) hμpos
  have hlt : (2 : ℝ) ^ ((e : ℤ) - j₀ - j₁ - 1) < ‖(F (n - k₀) : ℚ_[2]) * U k₀‖ := by
    rw [hterm₀, hνμ]; exact zpow_lt_zpow_right₀ one_lt_two (by omega)
  -- hence `‖[t^n] d‖ ≥ νμ > 2^{-c} 2^c = 1`, against the integrality of `d`
  have hD := norm_le_norm_of_hasSum_of_isolated (hconv n) k₀ hterm hlt
  rw [hterm₀, PadicInt.norm_coe] at hD
  have hone : (1 : ℝ) < ν * μ := by
    calc (1 : ℝ) = (2 : ℝ) ^ (-(c : ℤ)) * (2 : ℝ) ^ (c : ℤ) := by
          rw [← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero]
      _ < (2 : ℝ) ^ (-(c : ℤ)) * μ := mul_lt_mul_of_pos_left hμc (two_zpow_pos _)
      _ ≤ ν * μ := mul_le_mul_of_nonneg_right hνc hμpos.le
  exact absurd (hD.trans (PadicInt.norm_le_one _)) (not_le.mpr hone)

/-- **The base constant term** (tex 5703–5706). Since `f_0 ∈ Λ` has no negative powers of `t` and
`ũ_0 ∈ Λ[1/2]` has none either, `[t^0] d_0 = f_0(0) ũ_0(0)`. -/
theorem base_constant_term {F₀ : ℤ → ℤ_[2]} {U₀ : ℕ → ℚ_[2]} {D₀ : ℤ → ℤ_[2]}
    (hconv : HasSum (fun k : ℕ => (F₀ (0 - k) : ℚ_[2]) * U₀ k) (D₀ 0))
    (hΛ : ∀ i < 0, F₀ i = 0) :
    (D₀ 0 : ℚ_[2]) = F₀ 0 * U₀ 0 := by
  have h : HasSum (fun k : ℕ => (F₀ (0 - k) : ℚ_[2]) * U₀ k)
      ((F₀ (0 - ((0 : ℕ) : ℤ)) : ℚ_[2]) * U₀ 0) := by
    refine hasSum_single 0 fun k hk => ?_
    have hk' : (0 : ℤ) - k < 0 := by
      have : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      linarith
    simp only [hΛ _ hk', PadicInt.coe_zero, zero_mul]
  simpa using hconv.unique h

/-- **The base lower bound** (tex 5707–5709). Since `d_0` is integral and
`[t^0] d_0 = F_0 ũ_0(0)` with `v₂(F_0) = c`, `v₂ ũ_0(0) ≥ −c`, without using (5.5) at the base. -/
theorem base_lower_bound {F₀ : ℤ → ℤ_[2]} {U₀ : ℕ → ℚ_[2]} {D₀ : ℤ → ℤ_[2]} {c : ℕ}
    (hconv : HasSum (fun k : ℕ => (F₀ (0 - k) : ℚ_[2]) * U₀ k) (D₀ 0))
    (hΛ : ∀ i < 0, F₀ i = 0) (hF0 : F₀ 0 ≠ 0) (hc : (F₀ 0).valuation = c) :
    ‖U₀ 0‖ ≤ (2 : ℝ) ^ c := by
  have hD : ‖(D₀ 0 : ℚ_[2])‖ ≤ 1 := by rw [PadicInt.norm_coe]; exact PadicInt.norm_le_one _
  rw [base_constant_term hconv hΛ, norm_mul, PadicInt.norm_coe,
    norm_eq_two_zpow_neg_of_valuation hF0 hc] at hD
  calc ‖U₀ 0‖ = (2 : ℝ) ^ (c : ℤ) * ((2 : ℝ) ^ (-(c : ℤ)) * ‖U₀ 0‖) := by
        rw [← mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]
    _ ≤ (2 : ℝ) ^ (c : ℤ) * 1 := mul_le_mul_of_nonneg_left hD (zpow_pos two_pos _).le
    _ = (2 : ℝ) ^ c := by rw [mul_one, zpow_natCast]

/-- **The convolution** (tex 5710–5718). `[t^0] d_x = F_x ũ_x(0) + E_x`, where
`E_x = Σ_{i<0} [t^i] f_x · [t^{−i}] ũ_x` runs over *every* negative coefficient of `f_x`, and
`v₂(E_x) ≥ M − c` when every negative coefficient of `f_x` is divisible by `2^M` and
`v_𝒪(ũ_x) ≥ −c`. -/
theorem convolution_estimate {Fx : ℤ → ℤ_[2]} {Ux : ℕ → ℚ_[2]} {Dx : ℤ → ℤ_[2]} {c M : ℕ}
    (hconv : HasSum (fun k : ℕ => (Fx (0 - k) : ℚ_[2]) * Ux k) (Dx 0))
    (hU : ∀ n, ‖Ux n‖ ≤ (2 : ℝ) ^ c)
    (hneg : ∀ i < 0, (2 : ℤ_[2]) ^ M ∣ Fx i) :
    HasSum (fun k : ℕ => (Fx (-((k : ℤ) + 1)) : ℚ_[2]) * Ux (k + 1))
        ((Dx 0 : ℚ_[2]) - Fx 0 * Ux 0) ∧
      ‖(Dx 0 : ℚ_[2]) - Fx 0 * Ux 0‖ ≤ (2 : ℝ) ^ ((c : ℤ) - M) := by
  have hs : HasSum (fun k : ℕ => (Fx (-((k : ℤ) + 1)) : ℚ_[2]) * Ux (k + 1))
      ((Dx 0 : ℚ_[2]) - Fx 0 * Ux 0) := by
    have h := (hasSum_nat_add_iff' 1).mpr hconv
    have hfun : (fun k : ℕ => (Fx (-((k : ℤ) + 1)) : ℚ_[2]) * Ux (k + 1)) =
        fun k : ℕ => (Fx (0 - ((k + 1 : ℕ) : ℤ)) : ℚ_[2]) * Ux (k + 1) := by
      funext k
      rw [show (0 : ℤ) - ((k + 1 : ℕ) : ℤ) = -((k : ℤ) + 1) by push_cast; ring]
    rw [hfun]
    simpa using h
  refine ⟨hs, ?_⟩
  rw [← hs.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
  rw [norm_mul]
  calc ‖(Fx (-((k : ℤ) + 1)) : ℚ_[2])‖ * ‖Ux (k + 1)‖
      ≤ (2 : ℝ) ^ (-(M : ℤ)) * (2 : ℝ) ^ (c : ℤ) := by
        refine mul_le_mul (norm_coe_le_two_zpow_of_dvd (hneg (-((k : ℤ) + 1)) (by omega)))
          ?_ (norm_nonneg _) (zpow_pos two_pos _).le
        rw [zpow_natCast]; exact hU _
    _ = (2 : ℝ) ^ ((c : ℤ) - M) := by
        rw [← zpow_add₀ two_ne_zero]; congr 1; ring

/-- **The convolution estimate (5.11)** (tex 5694–5726; kind PROVED). At an address `x` where every
negative coefficient of `f_x` vanishes modulo `2^M`, its constant coefficient agrees with `f_0(0)`
modulo `2^M`, and the constant coefficient of `d_x` agrees with that of `d_0` modulo `2^M`, with
`c = v₂ f_0(0) < M`, `f_0 ∈ Λ`, `ũ_x ∈ Λ[1/2]` and `f ũ = d` at `x` and at `0`:
`v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c`. The proof is the text's: subtracting the two constant terms,
`F_x(ũ_x(0) − ũ_0(0)) = ([t^0]d_x − [t^0]d_0) − (F_x − F_0) ũ_0(0) − E_x`, every term on the right
has valuation at least `M − c`, and `v₂(F_x) = c`. -/
theorem difference_estimate {F₀ Fx : ℤ → ℤ_[2]} {U₀ Ux : ℕ → ℚ_[2]} {D₀ Dx : ℤ → ℤ_[2]}
    {c M : ℕ} (hUx : InLambdaHalf Ux)
    (hconv₀ : HasSum (fun k : ℕ => (F₀ (0 - k) : ℚ_[2]) * U₀ k) (D₀ 0))
    (hconvx : ∀ n : ℤ, HasSum (fun k : ℕ => (Fx (n - k) : ℚ_[2]) * Ux k) (Dx n))
    (hΛ : ∀ i < 0, F₀ i = 0) (hF0 : F₀ 0 ≠ 0) (hc : (F₀ 0).valuation = c) (hcM : c < M)
    (hneg : ∀ i < 0, (2 : ℤ_[2]) ^ M ∣ Fx i)
    (hF : (2 : ℤ_[2]) ^ M ∣ Fx 0 - F₀ 0)
    (hD : (2 : ℤ_[2]) ^ M ∣ Dx 0 - D₀ 0) :
    ‖Ux 0 - U₀ 0‖ ≤ (2 : ℝ) ^ (2 * (c : ℤ) - M) := by
  have hF0n : ‖F₀ 0‖ = (2 : ℝ) ^ (-(c : ℤ)) := norm_eq_two_zpow_neg_of_valuation hF0 hc
  have hMc : (2 : ℝ) ^ (-(M : ℤ)) < (2 : ℝ) ^ (-(c : ℤ)) :=
    zpow_lt_zpow_right₀ one_lt_two (by omega)
  have hFd : ‖Fx 0 - F₀ 0‖ < (2 : ℝ) ^ (-(c : ℤ)) :=
    (norm_le_two_zpow_of_dvd hF).trans_lt hMc
  -- `v₂(F_x) = c`
  have hFx0n : ‖Fx 0‖ = (2 : ℝ) ^ (-(c : ℤ)) := by
    have h2 : ‖F₀ 0‖ ≠ ‖Fx 0 - F₀ 0‖ := by rw [hF0n]; exact hFd.ne'
    rw [show Fx 0 = F₀ 0 + (Fx 0 - F₀ 0) by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2, hF0n]
    exact max_eq_left hFd.le
  have hFx0 : Fx 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hFx0n
    exact absurd hFx0n (zpow_pos two_pos _).ne
  have hcx : (Fx 0).valuation = c := by
    have h1 := PadicInt.norm_eq_zpow_neg_valuation hFx0
    rw [hFx0n] at h1
    push_cast at h1
    have := zpow_right_injective₀ (a := (2 : ℝ)) two_pos (by norm_num) h1
    omega
  have hnegx : ∀ i < 0, (2 : ℤ_[2]) ^ (c + 1) ∣ Fx i := fun i hi =>
    (pow_dvd_pow 2 (by omega : c + 1 ≤ M)).trans (hneg i hi)
  -- the Gauss step, the convolution at `x`, and the base
  have hUb := gauss_lower_bound hUx hconvx hFx0 hcx hnegx
  obtain ⟨-, hE⟩ := convolution_estimate (hconvx 0) hUb hneg
  have hbase := base_constant_term hconv₀ hΛ
  have hU0 := base_lower_bound hconv₀ hΛ hF0 hc
  -- `F_x (ũ_x(0) − ũ_0(0)) = ([t^0]d_x − [t^0]d_0) − (F_x − F_0) ũ_0(0) − E_x`
  have key : (Fx 0 : ℚ_[2]) * (Ux 0 - U₀ 0) =
      (((Dx 0 : ℚ_[2]) - D₀ 0) - ((Fx 0 : ℚ_[2]) - F₀ 0) * U₀ 0) -
        ((Dx 0 : ℚ_[2]) - Fx 0 * Ux 0) := by
    rw [hbase]; ring
  have hcM' : (2 : ℝ) ^ (-(M : ℤ)) ≤ (2 : ℝ) ^ ((c : ℤ) - M) :=
    zpow_le_zpow_right₀ one_le_two (by omega)
  have t1 : ‖(Dx 0 : ℚ_[2]) - D₀ 0‖ ≤ (2 : ℝ) ^ ((c : ℤ) - M) := by
    rw [← PadicInt.coe_sub]
    exact (norm_coe_le_two_zpow_of_dvd hD).trans hcM'
  have t2 : ‖((Fx 0 : ℚ_[2]) - F₀ 0) * U₀ 0‖ ≤ (2 : ℝ) ^ ((c : ℤ) - M) := by
    rw [norm_mul, ← PadicInt.coe_sub]
    calc ‖((Fx 0 - F₀ 0 : ℤ_[2]) : ℚ_[2])‖ * ‖U₀ 0‖
        ≤ (2 : ℝ) ^ (-(M : ℤ)) * (2 : ℝ) ^ (c : ℤ) := by
          refine mul_le_mul (norm_coe_le_two_zpow_of_dvd hF) ?_ (norm_nonneg _)
            (zpow_pos two_pos _).le
          rw [zpow_natCast]; exact hU0
      _ = (2 : ℝ) ^ ((c : ℤ) - M) := by
          rw [← zpow_add₀ two_ne_zero]; congr 1; ring
  have hsum : ‖(Fx 0 : ℚ_[2]) * (Ux 0 - U₀ 0)‖ ≤ (2 : ℝ) ^ ((c : ℤ) - M) := by
    rw [key]
    exact padic_norm_sub_le_of_le (padic_norm_sub_le_of_le t1 t2) hE
  -- divide by `‖F_x‖ = 2^{-c}`
  rw [norm_mul, PadicInt.norm_coe, hFx0n] at hsum
  calc ‖Ux 0 - U₀ 0‖ = (2 : ℝ) ^ (c : ℤ) * ((2 : ℝ) ^ (-(c : ℤ)) * ‖Ux 0 - U₀ 0‖) := by
        rw [← mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]
    _ ≤ (2 : ℝ) ^ (c : ℤ) * (2 : ℝ) ^ ((c : ℤ) - M) :=
        mul_le_mul_of_nonneg_left hsum (zpow_pos two_pos _).le
    _ = (2 : ℝ) ^ (2 * (c : ℤ) - M) := by
        rw [← zpow_add₀ two_ne_zero]; congr 1; ring

end ZInQ.Manuscript.RC.Boolean
