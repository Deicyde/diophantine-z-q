import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Character sums over finite fields for the good primes of Proposition 0

File 6 of `docs/research/nt-prop0.md` §4.1: everything over `𝔽_p` that Lemma G2 (§2.3) needs, with
no `p`-adic content. Over a finite field `F` of odd characteristic, with `χ = quadraticChar F`:

* Lemma Q, `sum_quadraticChar_mul_sub`: `Σ_ξ χ((ξ - e)(ξ - e')) = -1` for `e ≠ e'`;
* the cubic sum `cubicCharSum n = Σ_ξ χ(ξ³ - nξ)` and Lemma J (Jacobsthal), in the forms
  `cubicCharSum_one_sq_le : S(1)² ≤ 4q` and `cubicCharSum_sq_le : S(n)² ≤ 4q` for `n` a nonzero
  square;
* the count `eight_mul_card_ge : 8N ≥ q - 15 - |S(d²)|` for the number `N` of `ξ ∉ {0, ±d}` with
  prescribed characters of `ξ`, `ξ - d` and `ξ + d`;
* `exists_xi`, Step 1 of §2.3: for `p` an odd prime and `a, b, d` nonzero in `ZMod p`, either `a`
  and `b` are squares, or some `ξ` makes `ξ / a`, `(ξ - d) / b` and `(ξ + d) / (ab)` squares. For
  `p ≥ 29` it comes from the count (`exists_xi_of_card`, valid for any finite field with at least
  `26` elements); for `p < 29` from a `Nat`-valued Boolean checker run by `decide +kernel`.
-/

namespace ZInQ.RouteK.Selmer

open Finset

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- Lemma Q: `Σ_ξ χ((ξ - e)(ξ - e')) = -1` for `e ≠ e'`, from `jacobiSum_nontrivial_inv`. -/
theorem sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) {e e' : F} (h : e ≠ e') :
    ∑ ξ : F, χ ((ξ - e) * (ξ - e')) = -1 := by
  have hc : e' - e ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  -- substitute ξ = e + (e' - e) t
  have hsub : ∑ ξ : F, χ ((ξ - e) * (ξ - e')) = ∑ t : F, χ ((e + (e' - e) * t - e) *
      (e + (e' - e) * t - e')) := by
    refine (Fintype.sum_bijective (fun t => e + (e' - e) * t) ?_ _ _ fun t => rfl).symm
    refine ⟨fun a b hab => ?_, fun ξ => ⟨(ξ - e) / (e' - e), ?_⟩⟩
    · simpa [hc] using hab
    · field_simp; ring
  have hterm : ∀ t : F, χ ((e + (e' - e) * t - e) * (e + (e' - e) * t - e')) =
      χ (-1) * (χ t * χ (1 - t)) := by
    intro t
    have : (e + (e' - e) * t - e) * (e + (e' - e) * t - e') =
        (e' - e) ^ 2 * ((-1) * (t * (1 - t))) := by
      ring
    rw [this, map_mul, quadraticChar_sq_one' hc, one_mul, map_mul, map_mul]
  rw [hsub, Finset.sum_congr rfl fun t _ => hterm t, ← Finset.mul_sum]
  have hJ : ∑ t : F, χ t * χ (1 - t) = -χ (-1) := by
    have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv, jacobiSum] at this
  rw [hJ, mul_neg, ← map_mul, neg_one_mul, neg_neg, map_one]

/-- `Σ_ξ χ((ξ - e)²) = q - 1`. -/
theorem sum_quadraticChar_sub_sq (e : F) :
    ∑ ξ : F, χ ((ξ - e) * (ξ - e)) = Fintype.card F - 1 := by
  have h : ∀ ξ : F, χ ((ξ - e) * (ξ - e)) = 1 - if ξ = e then 1 else 0 := by
    intro ξ
    by_cases hξ : ξ = e
    · simp [hξ]
    · rw [← sq, quadraticChar_sq_one' (sub_ne_zero.mpr hξ)]; simp [hξ]
  rw [Finset.sum_congr rfl fun ξ _ => h ξ, Finset.sum_sub_distrib]
  simp

/-- The values of `χ` are `-1`, `0` or `1`; in particular `χ(a)³ = χ(a)`. -/
theorem quadraticChar_pow_three (a : F) : χ a ^ 3 = χ a := by
  rcases (quadraticChar_isQuadratic F) a with h | h | h <;> rw [h] <;> norm_num

theorem quadraticChar_abs_le_one (a : F) : |χ a| ≤ 1 := by
  rcases (quadraticChar_isQuadratic F) a with h | h | h <;> rw [h] <;> norm_num

/-- The cubic character sum `S(n) = Σ_ξ χ(ξ³ - nξ)` of §2.3. -/
def cubicCharSum (n : F) : ℤ := ∑ ξ : F, χ (ξ ^ 3 - n * ξ)

/-- Square-class invariance: `S(n t²) = χ(t) S(n)` for `t ≠ 0`. -/
theorem cubicCharSum_mul_sq (n : F) {t : F} (ht : t ≠ 0) :
    cubicCharSum (n * t ^ 2) = χ t * cubicCharSum n := by
  unfold cubicCharSum
  rw [Finset.mul_sum]
  refine (Fintype.sum_bijective (fun η => t * η) ?_ _ _ fun η => ?_).symm
  · refine ⟨fun a b hab => mul_left_cancel₀ ht hab, fun ξ => ⟨ξ / t, ?_⟩⟩
    field_simp
  · have : (t * η) ^ 3 - n * t ^ 2 * (t * η) = t ^ 3 * (η ^ 3 - n * η) := by ring
    simp only [this, map_mul, map_pow, quadraticChar_pow_three]

/-- `S(0) = 0`. -/
theorem cubicCharSum_zero (hF : ringChar F ≠ 2) : cubicCharSum (0 : F) = 0 := by
  unfold cubicCharSum
  simp only [zero_mul, sub_zero, map_pow, quadraticChar_pow_three]
  exact quadraticChar_sum_zero hF

/-- The inner sum over `n` in Jacobsthal's identity. -/
theorem sum_quadraticChar_sq_sub (hF : ringChar F ≠ 2) (ξ η : F) :
    ∑ n : F, χ ((n - ξ ^ 2) * (n - η ^ 2)) =
      (Fintype.card F : ℤ) * (if ξ ^ 2 = η ^ 2 then 1 else 0) - 1 := by
  by_cases h : ξ ^ 2 = η ^ 2
  · rw [← h, sum_quadraticChar_sub_sq]; simp
  · rw [sum_quadraticChar_mul_sub hF h]; simp [h]

/-- The sum over `η` with `η² = ξ²` in Jacobsthal's identity. -/
theorem sum_quadraticChar_mul_sq_eq (hF : ringChar F ≠ 2) (ξ : F) :
    ∑ η : F, χ (ξ * η) * (if ξ ^ 2 = η ^ 2 then 1 else 0) =
      if ξ = 0 then 0 else 1 + χ (-1) := by
  by_cases hξ : ξ = 0
  · simp [hξ]
  simp only [hξ, ite_false]
  have hne : ξ ≠ -ξ := fun h => hξ ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
  have hset : (univ.filter fun η : F => ξ ^ 2 = η ^ 2) = {ξ, -ξ} := by
    ext η
    simp [eq_comm (a := ξ ^ 2), sq_eq_sq_iff_eq_or_eq_neg, eq_comm (a := η)]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, hset, Finset.sum_pair hne, ← sq, quadraticChar_sq_one' hξ]
  have : ξ * -ξ = (-1) * ξ ^ 2 := by ring
  rw [this, map_mul, quadraticChar_sq_one' hξ, mul_one]

/-- Jacobsthal's identity: `Σ_n S(n)² = q(q - 1)(1 + χ(-1))`. -/
theorem sum_cubicCharSum_sq (hF : ringChar F ≠ 2) :
    ∑ n : F, cubicCharSum n ^ 2 =
      (Fintype.card F : ℤ) * (Fintype.card F - 1) * (1 + χ (-1)) := by
  have hexp : ∀ n : F, cubicCharSum n ^ 2 =
      ∑ ξ : F, ∑ η : F, χ (ξ * η) * χ ((n - ξ ^ 2) * (n - η ^ 2)) := by
    intro n
    rw [sq, cubicCharSum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => Finset.sum_congr rfl fun η _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  have hinner : ∀ ξ η : F, ∑ n : F, χ (ξ * η) * χ ((n - ξ ^ 2) * (n - η ^ 2)) =
      (Fintype.card F : ℤ) * (χ (ξ * η) * (if ξ ^ 2 = η ^ 2 then 1 else 0)) - χ ξ * χ η := by
    intro ξ η
    rw [← Finset.mul_sum, sum_quadraticChar_sq_sub hF, map_mul]; ring
  have hcard : ((univ.filter fun ξ : F => ¬ξ = 0).card : ℤ) = Fintype.card F - 1 := by
    rw [Finset.filter_ne' univ (0 : F), Finset.card_erase_of_mem (mem_univ _), card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  calc ∑ n : F, cubicCharSum n ^ 2
      = ∑ ξ : F, ∑ η : F, ∑ n : F, χ (ξ * η) * χ ((n - ξ ^ 2) * (n - η ^ 2)) := by
        simp only [hexp]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ξ _ => Finset.sum_comm
    _ = (Fintype.card F : ℤ) * ∑ ξ : F, (if ξ = 0 then 0 else 1 + χ (-1)) -
          (∑ ξ : F, χ ξ) * ∑ η : F, χ η := by
        simp only [hinner, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_mul_sum,
          sum_quadraticChar_mul_sq_eq hF]
    _ = _ := by
        rw [quadraticChar_sum_zero hF, mul_zero, sub_zero, Finset.sum_ite, Finset.sum_const_zero,
          zero_add, Finset.sum_const, nsmul_eq_mul, hcard]
        ring

/-- `Σ_t S(t²)² ≤ 2 Σ_n S(n)²`, since `t ↦ t²` has fibres of size `1 + χ(n) ≤ 2`. -/
theorem sum_cubicCharSum_sq_comp_sq_le (hF : ringChar F ≠ 2) :
    ∑ t : F, cubicCharSum (t ^ 2) ^ 2 ≤ 2 * ∑ n : F, cubicCharSum n ^ 2 := by
  rw [← Finset.sum_fiberwise univ (fun t : F => t ^ 2) (fun t => cubicCharSum (t ^ 2) ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  have hfib : (univ.filter fun t : F => t ^ 2 = n).card = χ n + 1 := by
    rw [← quadraticChar_card_sqrts hF n]
    congr 2
    ext t; simp
  rw [Finset.sum_congr rfl fun t ht => by rw [(Finset.mem_filter.mp ht).2], Finset.sum_const,
    nsmul_eq_mul, hfib]
  have h1 : χ n ≤ 1 := (abs_le.mp (quadraticChar_abs_le_one n)).2
  nlinarith [sq_nonneg (cubicCharSum n)]

/-- Lemma J (Jacobsthal): `S(1)² ≤ 4q`. -/
theorem cubicCharSum_one_sq_le (hF : ringChar F ≠ 2) :
    cubicCharSum (1 : F) ^ 2 ≤ 4 * Fintype.card F := by
  have hS : ∀ t : F, t ≠ 0 → cubicCharSum (t ^ 2) ^ 2 = cubicCharSum (1 : F) ^ 2 := by
    intro t ht
    have := cubicCharSum_mul_sq (1 : F) ht
    rw [one_mul] at this
    rw [this, mul_pow, quadraticChar_sq_one ht, one_mul]
  have hsum : ∑ t : F, cubicCharSum (t ^ 2) ^ 2 =
      (Fintype.card F - 1 : ℤ) * cubicCharSum (1 : F) ^ 2 := by
    rw [← Finset.sum_erase_add univ _ (mem_univ (0 : F))]
    rw [Finset.sum_congr rfl fun t ht => hS t (Finset.ne_of_mem_erase ht), Finset.sum_const,
      Finset.card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
      Nat.cast_sub Fintype.card_pos]
    simp [cubicCharSum_zero hF]
  have hle := sum_cubicCharSum_sq_comp_sq_le hF
  rw [hsum, sum_cubicCharSum_sq hF] at hle
  have hm : χ (-1) ≤ 1 := (abs_le.mp (quadraticChar_abs_le_one _)).2
  have hq : (1 : ℤ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hq0 : (0 : ℤ) ≤ Fintype.card F := by positivity
  have h2 : (Fintype.card F - 1 : ℤ) * cubicCharSum (1 : F) ^ 2 ≤
      (Fintype.card F - 1 : ℤ) * (4 * Fintype.card F) := by
    refine hle.trans ?_
    nlinarith [mul_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hq.le)) (sub_nonneg.mpr hm)]
  exact le_of_mul_le_mul_left h2 (by linarith)

/-- Lemma J for a nonzero square: `S(d²)² ≤ 4q`. -/
theorem cubicCharSum_sq_le (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    cubicCharSum (d ^ 2) ^ 2 ≤ 4 * Fintype.card F := by
  have := cubicCharSum_mul_sq (1 : F) hd
  rw [one_mul] at this
  rw [this, mul_pow, quadraticChar_sq_one hd, one_mul]
  exact cubicCharSum_one_sq_le hF

/-- `Σ_ξ χ(ξ - e) = 0`. -/
theorem sum_quadraticChar_sub (hF : ringChar F ≠ 2) (e : F) : ∑ ξ : F, χ (ξ - e) = 0 := by
  rw [Fintype.sum_equiv (Equiv.subRight e) (fun ξ => χ (ξ - e)) (fun ξ => χ ξ) fun ξ => rfl]
  exact quadraticChar_sum_zero hF

/-- For `γ = ±1`, the factor `1 + γ χ(x)` lies in `[0, 2]`. -/
theorem one_add_mul_quadraticChar_mem {γ : ℤ} (hγ : γ = 1 ∨ γ = -1) (x : F) :
    0 ≤ 1 + γ * χ x ∧ 1 + γ * χ x ≤ 2 := by
  have := abs_le.mp (quadraticChar_abs_le_one x)
  rcases hγ with rfl | rfl <;> constructor <;> linarith

/-- For `x ≠ 0` and `γ = ±1`, `1 + γ χ(x)` is `2` if `χ(x) = γ` and `0` otherwise. -/
theorem one_add_mul_quadraticChar_eq {γ : ℤ} (hγ : γ = 1 ∨ γ = -1) {x : F} (hx : x ≠ 0) :
    1 + γ * χ x = if χ x = γ then 2 else 0 := by
  rcases quadraticChar_dichotomy hx with h | h <;> rcases hγ with rfl | rfl <;> simp [h]

/-- The number `N` of Step 2 of §2.3: the `ξ ∉ {0, ±d}` with `χ(ξ) = α`, `χ(ξ - d) = β` and
`χ(ξ + d) = αβ`. -/
def fibreCard (d : F) (α β : ℤ) : ℕ :=
  (univ.filter fun ξ : F => (ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d) ∧
    (χ ξ = α ∧ χ (ξ - d) = β ∧ χ (ξ + d) = α * β)).card

/-- The count of Step 2 of §2.3: `8N ≥ q - 15 - |S(d²)|`. -/
theorem eight_mul_fibreCard_ge (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) {α β : ℤ}
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) :
    (Fintype.card F : ℤ) - 15 - |cubicCharSum (d ^ 2)| ≤ 8 * fibreCard d α β := by
  set P : F → ℤ := fun ξ => (1 + α * χ ξ) * (1 + β * χ (ξ - d)) * (1 + α * β * χ (ξ + d))
    with hPdef
  have hαβ : α * β = 1 ∨ α * β = -1 := by
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> simp
  have hα2 : α ^ 2 = 1 := by rcases hα with rfl | rfl <;> simp
  have hβ2 : β ^ 2 = 1 := by rcases hβ with rfl | rfl <;> simp
  -- the sum over all of `F`
  have hP : ∀ ξ : F, P ξ = 1 + α * χ (ξ - 0) + β * χ (ξ - d) + α * β * χ (ξ - -d) +
      α * β * χ ((ξ - 0) * (ξ - d)) + β * χ ((ξ - 0) * (ξ - -d)) +
      α * χ ((ξ - d) * (ξ - -d)) + χ (ξ ^ 3 - d ^ 2 * ξ) := by
    intro ξ
    have hc : ξ ^ 3 - d ^ 2 * ξ = ξ * (ξ - d) * (ξ + d) := by ring
    simp only [hPdef, hc, map_mul, sub_zero, sub_neg_eq_add]
    linear_combination (β * χ ξ * χ (ξ + d) + χ ξ * χ (ξ - d) * χ (ξ + d)) * hα2 +
      (α * χ (ξ - d) * χ (ξ + d) + α ^ 2 * χ ξ * χ (ξ - d) * χ (ξ + d)) * hβ2
  have hd' : (0 : F) ≠ -d := by simpa [eq_comm] using hd
  have hdd : d ≠ -d := fun h => hd ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
  have hall : ∑ ξ : F, P ξ = Fintype.card F - α * β - β - α + cubicCharSum (d ^ 2) := by
    simp only [hP, Finset.sum_add_distrib, ← Finset.mul_sum, sum_quadraticChar_sub hF,
      sum_quadraticChar_mul_sub hF (Ne.symm hd), sum_quadraticChar_mul_sub hF hd',
      sum_quadraticChar_mul_sub hF hdd, cubicCharSum]
    simp only [mul_zero, add_zero, mul_neg, mul_one, Finset.sum_const, card_univ, nsmul_eq_mul]
    ring
  -- the sum over `ξ ∉ {0, ±d}` is `8N`
  have hgood : ∑ ξ ∈ univ.filter (fun ξ : F => ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d), P ξ =
      8 * fibreCard d α β := by
    have hN : fibreCard d α β = ((univ.filter fun ξ : F => ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d).filter
        fun ξ => χ ξ = α ∧ χ (ξ - d) = β ∧ χ (ξ + d) = α * β).card := by
      rw [fibreCard, Finset.filter_filter]
    rw [hN, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    obtain ⟨h0, h1, h2⟩ := (Finset.mem_filter.mp hξ).2
    have e1 := one_add_mul_quadraticChar_eq hα h0
    have e2 := one_add_mul_quadraticChar_eq hβ (sub_ne_zero.mpr h1)
    have e3 := one_add_mul_quadraticChar_eq hαβ (show ξ + d ≠ 0 from fun h =>
      h2 (eq_neg_of_add_eq_zero_left h))
    simp only [hPdef, e1, e2, e3]
    split_ifs <;> simp_all
  -- the excluded points contribute at most `12`
  have hbad : ∑ ξ ∈ univ.filter (fun ξ : F => ¬(ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d)), P ξ ≤ 12 := by
    have hsub : univ.filter (fun ξ : F => ¬(ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d)) ⊆ {0, d, -d} := by
      intro ξ hξ
      simp only [Finset.mem_filter, mem_univ, true_and, not_and_or, not_not] at hξ
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hcard := (Finset.card_le_card hsub).trans Finset.card_le_three
    have hle : ∀ ξ ∈ univ.filter (fun ξ : F => ¬(ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d)), P ξ ≤ 4 := by
      intro ξ hξ
      have f1 := one_add_mul_quadraticChar_mem hα ξ
      have f2 := one_add_mul_quadraticChar_mem hβ (ξ - d)
      have f3 := one_add_mul_quadraticChar_mem hαβ (ξ + d)
      simp only [Finset.mem_filter, mem_univ, true_and, not_and_or, not_not] at hξ
      simp only [hPdef]
      rcases hξ with rfl | rfl | rfl
      · simp only [quadraticChar_zero, mul_zero, add_zero, one_mul]; nlinarith
      · simp only [sub_self, quadraticChar_zero, mul_zero, add_zero, mul_one]; nlinarith
      · simp only [neg_add_cancel, quadraticChar_zero, mul_zero, add_zero, mul_one]; nlinarith
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans ?_
    rw [nsmul_eq_mul]
    have : ((univ.filter (fun ξ : F => ¬(ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d))).card : ℤ) ≤ 3 := by
      exact_mod_cast hcard
    linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not univ
    (fun ξ : F => ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d) P
  rw [hgood, hall] at hsplit
  have h1 : α * β ≤ 1 := by rcases hαβ with h | h <;> linarith
  have h2 : α ≤ 1 := by rcases hα with h | h <;> linarith
  have h3 : β ≤ 1 := by rcases hβ with h | h <;> linarith
  have h4 := neg_abs_le (cubicCharSum (d ^ 2))
  linarith

/-- For `q ≥ 26` the fibre of Step 2 is nonempty: `S(d²)² ≤ 4q < (q - 15)²`. -/
theorem fibreCard_pos (hF : ringChar F ≠ 2) (hq : 26 ≤ Fintype.card F) {d : F} (hd : d ≠ 0)
    {α β : ℤ} (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) : 0 < fibreCard d α β := by
  have hc := eight_mul_fibreCard_ge hF hd hα hβ
  have hJ := cubicCharSum_sq_le hF hd
  have hq' : (26 : ℤ) ≤ Fintype.card F := by exact_mod_cast hq
  by_contra h0
  have h0' : (fibreCard d α β : ℤ) = 0 := by exact_mod_cast Nat.eq_zero_of_not_pos h0
  rw [h0', mul_zero] at hc
  have habs : (Fintype.card F : ℤ) - 15 ≤ |cubicCharSum (d ^ 2)| := by linarith
  have hsq : ((Fintype.card F : ℤ) - 15) ^ 2 ≤ cubicCharSum (d ^ 2) ^ 2 := by
    rw [← sq_abs (cubicCharSum (d ^ 2))]
    exact pow_le_pow_left₀ (by linarith) habs 2
  nlinarith

/-- `χ(c) = χ(a)` with `a ≠ 0` makes `c / a` a square. -/
theorem isSquare_div_of_quadraticChar_eq {a c : F} (ha : a ≠ 0) (h : χ c = χ a) :
    IsSquare (c / a) := by
  by_cases hc : c = 0
  · rw [hc, zero_div]; exact IsSquare.zero
  refine (quadraticChar_one_iff_isSquare (div_ne_zero hc ha)).mp ?_
  have : c / a = c * a * (a⁻¹) ^ 2 := by field_simp
  rw [this, map_mul, quadraticChar_sq_one' (inv_ne_zero ha), mul_one, map_mul, h, ← sq,
    quadraticChar_sq_one ha]

/-- Step 1 of §2.3 for fields with at least `26` elements, with `ξ ∉ {0, ±d}`. -/
theorem exists_xi_of_card (hF : ringChar F ≠ 2) (hq : 26 ≤ Fintype.card F) {d a b : F}
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ ξ : F, ξ ≠ 0 ∧ ξ ≠ d ∧ ξ ≠ -d ∧
      IsSquare (ξ / a) ∧ IsSquare ((ξ - d) / b) ∧ IsSquare ((ξ + d) / (a * b)) := by
  obtain ⟨ξ, hξ⟩ := Finset.card_pos.mp (fibreCard_pos hF hq hd (quadraticChar_dichotomy ha)
    (quadraticChar_dichotomy hb))
  obtain ⟨⟨h0, h1, h2⟩, e1, e2, e3⟩ := (Finset.mem_filter.mp hξ).2
  refine ⟨ξ, h0, h1, h2, isSquare_div_of_quadraticChar_eq ha e1,
    isSquare_div_of_quadraticChar_eq hb e2, isSquare_div_of_quadraticChar_eq (mul_ne_zero ha hb) ?_⟩
  rw [e3, map_mul]

end Field

section Small

/-! ### Small primes: a `Nat`-valued checker run by `decide +kernel` -/

/-- Euler's criterion on `ℕ`: `x^(p/2) mod p`, which is `1` on squares and `p - 1` on non-squares. -/
def eulerNat (p x : ℕ) : ℕ := Nat.pow x (p / 2) % p

/-- `ξ` witnesses Step 1 for `d̄ = dv` and the classes `al`, `be` (each `1` or `p - 1`). -/
def xiOK (p dv al be ξ : ℕ) : Bool :=
  (ξ == 0 || eulerNat p ξ == al) && (ξ == dv || eulerNat p (ξ + p - dv) == be) &&
    (ξ + dv == p || eulerNat p (ξ + dv) == al * be % p)

/-- Step 1 at `p` for every `d̄ ≠ 0` and every pair of classes except the trivial one. -/
def xiCheckPrime (p : ℕ) : Bool :=
  (List.range p).all fun dv => dv == 0 ||
    [(1, p - 1), (p - 1, 1), (p - 1, p - 1)].all fun c =>
      (List.range p).any fun ξ => xiOK p dv c.1 c.2 ξ

/-- The odd primes below `29`. -/
def xiSmallPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23]

theorem xiCheck_small : xiSmallPrimes.all xiCheckPrime = true := by decide +kernel

variable {p : ℕ} [hp : Fact p.Prime]

theorem eulerNat_cast (x : ℕ) : ((eulerNat p x : ℕ) : ZMod p) = (x : ZMod p) ^ (p / 2) := by
  rw [eulerNat, ZMod.natCast_mod, Nat.pow_eq, Nat.cast_pow]

/-- Euler's criterion for quotients: `c^(p/2) = a^(p/2)` with `a ≠ 0` makes `c / a` a square. -/
theorem isSquare_div_of_pow_eq {a c : ZMod p} (ha : a ≠ 0) (h : c = 0 ∨ c ^ (p / 2) = a ^ (p / 2)) :
    IsSquare (c / a) := by
  rcases h with h | h
  · rw [h, zero_div]; exact IsSquare.zero
  by_cases hc : c = 0
  · rw [hc, zero_div]; exact IsSquare.zero
  rw [ZMod.euler_criterion p (div_ne_zero hc ha), div_pow, h, div_self (pow_ne_zero _ ha)]

/-- The checker's witness gives the three squares of Step 1. -/
theorem xi_of_xiOK {d a b : ZMod p} {dv al be ξ : ℕ} (hdv : dv < p) (hd : (dv : ZMod p) = d)
    (ha : a ≠ 0) (hb : b ≠ 0) (hal : (al : ZMod p) = a ^ (p / 2))
    (hbe : (be : ZMod p) = b ^ (p / 2)) (h : xiOK p dv al be ξ = true) :
    IsSquare ((ξ : ZMod p) / a) ∧ IsSquare (((ξ : ZMod p) - d) / b) ∧
      IsSquare (((ξ : ZMod p) + d) / (a * b)) := by
  simp only [xiOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨isSquare_div_of_pow_eq ha ?_, isSquare_div_of_pow_eq hb ?_,
    isSquare_div_of_pow_eq (mul_ne_zero ha hb) ?_⟩
  · rcases h1 with h1 | h1
    · left; rw [h1, Nat.cast_zero]
    · right; rw [← eulerNat_cast, h1, hal]
  · have hcast : ((ξ + p - dv : ℕ) : ZMod p) = (ξ : ZMod p) - d := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero, hd]
    rcases h2 with h2 | h2
    · left; rw [h2, hd, sub_self]
    · right; rw [← hcast, ← eulerNat_cast, h2, hbe]
  · rcases h3 with h3 | h3
    · left; rw [← hd, ← Nat.cast_add, h3, ZMod.natCast_self]
    · right; rw [← hd, ← Nat.cast_add, ← eulerNat_cast, h3, ZMod.natCast_mod, Nat.cast_mul, hal,
        hbe, mul_pow]

/-- The class `a^(p/2)` of `a ≠ 0` as a natural number: `1` or `p - 1`. -/
theorem exists_classNat {a : ZMod p} (ha : a ≠ 0) :
    (a ^ (p / 2) = 1 ∧ ((1 : ℕ) : ZMod p) = a ^ (p / 2)) ∨
      (a ^ (p / 2) = -1 ∧ ((p - 1 : ℕ) : ZMod p) = a ^ (p / 2)) := by
  rcases ZMod.pow_div_two_eq_neg_one_or_one p ha with h | h
  · left; rw [h, Nat.cast_one]; exact ⟨rfl, rfl⟩
  · right
    rw [h, Nat.cast_sub hp.out.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    exact ⟨rfl, rfl⟩

/-- Step 1 of §2.3 for the primes `p ∈ {3, …, 23}`, from the checker. -/
theorem exists_xi_of_check (hcheck : xiCheckPrime p = true) {d a b : ZMod p} (hd : d ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsSquare a ∧ IsSquare b) ∨
      ∃ ξ : ZMod p, IsSquare (ξ / a) ∧ IsSquare ((ξ - d) / b) ∧ IsSquare ((ξ + d) / (a * b)) := by
  have hdv : d.val < p := ZMod.val_lt d
  have hdv0 : d.val ≠ 0 := fun h => hd ((ZMod.val_eq_zero d).mp h)
  have hdd : (d.val : ZMod p) = d := ZMod.natCast_zmod_val d
  have key : ∀ al be : ℕ, (al, be) ∈ [(1, p - 1), (p - 1, 1), (p - 1, p - 1)] →
      (al : ZMod p) = a ^ (p / 2) → (be : ZMod p) = b ^ (p / 2) →
      ∃ ξ : ZMod p, IsSquare (ξ / a) ∧ IsSquare ((ξ - d) / b) ∧
        IsSquare ((ξ + d) / (a * b)) := by
    intro al be hmem hal hbe
    simp only [xiCheckPrime, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      List.any_eq_true] at hcheck
    obtain ⟨ξ, -, hξ⟩ := (hcheck d.val hdv).resolve_left hdv0 (al, be) hmem
    exact ⟨ξ, xi_of_xiOK hdv hdd ha hb hal hbe hξ⟩
  rcases exists_classNat ha with ⟨ha1, hal⟩ | ⟨-, hal⟩ <;>
    rcases exists_classNat hb with ⟨hb1, hbe⟩ | ⟨-, hbe⟩
  · left
    exact ⟨(ZMod.euler_criterion p ha).mpr ha1, (ZMod.euler_criterion p hb).mpr hb1⟩
  · exact Or.inr (key _ _ (by simp) hal hbe)
  · exact Or.inr (key _ _ (by simp) hal hbe)
  · exact Or.inr (key _ _ (by simp) hal hbe)

/-- **Step 1 of §2.3.** For an odd prime `p` and `d, a, b` nonzero in `𝔽_p`: either `a` and `b` are
squares, or there is `ξ` with `ξ / a`, `(ξ - d) / b` and `(ξ + d) / (ab)` squares (zero allowed).
For `p ≥ 29` from the count; for `p < 29` from the checker `xiCheck_small`. -/
theorem exists_xi (hp2 : p ≠ 2) {d a b : ZMod p} (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsSquare a ∧ IsSquare b) ∨
      ∃ ξ : ZMod p, IsSquare (ξ / a) ∧ IsSquare ((ξ - d) / b) ∧ IsSquare ((ξ + d) / (a * b)) := by
  by_cases hlarge : 29 ≤ p
  · right
    have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
    have hq : 26 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
    obtain ⟨ξ, -, -, -, h⟩ := exists_xi_of_card hF hq hd ha hb
    exact ⟨ξ, h⟩
  · have hmem : p ∈ xiSmallPrimes := by
      have hpp := hp.out
      interval_cases p <;> first
        | (simp [xiSmallPrimes]; done)
        | exact absurd rfl hp2
        | (exfalso; revert hpp; norm_num)
    have hcheck : xiCheckPrime p = true := List.all_eq_true.mp xiCheck_small p hmem
    exact exists_xi_of_check hcheck hd ha hb

end Small


end ZInQ.RouteK.Selmer
