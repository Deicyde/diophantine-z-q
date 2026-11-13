import Mathlib

/-!
# Additive discrete valuations `K → ℤ ∪ {∞}`

The local statements of the multiplication chapter are stated for an additive valuation
`v : AddValuation K (WithTop ℤ)` on a field `K`: `v 0 = ⊤`, `v (x y) = v x + v y` and
`v (x + y) ≥ min (v x) (v y)`. This file collects the bookkeeping used with such a valuation,
phrased through the predicate `Vge v m x : m ≤ v x` for an integer `m` (true for `x = 0`).
-/

namespace ZInQ.Mult

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))

/-- `v(x) ≥ m` for an integer `m` (always true for `x = 0`). -/
def Vge (m : ℤ) (x : K) : Prop := ((m : ℤ) : WithTop ℤ) ≤ v x

variable {v}

theorem val_eq_coe {x : K} (hx : x ≠ 0) : ∃ n : ℤ, v x = n := by
  have h : v x ≠ ⊤ := (v.ne_top_iff).mpr hx
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨n, hn.symm⟩

theorem vge_iff_of_eq {x : K} {n m : ℤ} (hn : v x = n) : Vge v m x ↔ m ≤ n := by
  rw [Vge, hn]; exact WithTop.coe_le_coe

theorem Vge.of_eq {x : K} {n : ℤ} (hn : v x = n) : Vge v n x := (vge_iff_of_eq hn).mpr le_rfl

namespace Vge

variable {m n : ℤ} {x y : K}

theorem zero (m : ℤ) : Vge v m 0 := by rw [Vge, v.map_zero]; exact le_top

theorem mono (h : Vge v m x) (hl : n ≤ m) : Vge v n x :=
  le_trans (WithTop.coe_le_coe.mpr hl) h

theorem add (hx : Vge v m x) (hy : Vge v m y) : Vge v m (x + y) := v.map_le_add hx hy

theorem neg (hx : Vge v m x) : Vge v m (-x) := by rwa [Vge, v.map_neg]

theorem sub (hx : Vge v m x) (hy : Vge v m y) : Vge v m (x - y) := v.map_le_sub hx hy

theorem mul (hx : Vge v m x) (hy : Vge v n y) : Vge v (m + n) (x * y) := by
  unfold Vge; rw [v.map_mul, WithTop.coe_add]; exact add_le_add hx hy

theorem pow (hx : Vge v m x) (k : ℕ) : Vge v (k * m) (x ^ k) := by
  induction k with
  | zero => rw [pow_zero, Vge, v.map_one]; simp
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul hx
    exact this.mono (by push_cast; linarith)

/-- Division by an element of valuation `0`. -/
theorem div_unit (hx : Vge v m x) {u : K} (hu : v u = 0) : Vge v m (x / u) := by
  rw [Vge, v.map_div, hu, sub_zero]; exact hx

theorem div_val' {e : ℤ} (hx : Vge v m x) (hy : v y = e) : Vge v (m - e) (x / y) := by
  by_cases h : x = 0
  · subst h; rw [zero_div]; exact Vge.zero _
  obtain ⟨n, hn⟩ := val_eq_coe h
  rw [Vge, v.map_div, hn, hy]
  have := WithTop.coe_le_coe.mp (hn ▸ hx : ((m : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ))
  exact WithTop.coe_le_coe.mpr (by omega)

theorem sum_of_le {ι : Type*} {s : Finset ι} {f : ι → K} (h : ∀ i ∈ s, Vge v m (f i)) :
    Vge v m (∑ i ∈ s, f i) := v.map_le_sum h

end Vge

theorem vge_natCast (n : ℕ) : Vge v 0 (n : K) := by
  induction n with
  | zero => simpa using Vge.zero (v := v) 0
  | succ n ih =>
    push_cast
    refine ih.add ?_
    rw [Vge, v.map_one]; simp

theorem vge_ofNat (n : ℕ) [n.AtLeastTwo] : Vge v 0 (OfNat.ofNat n : K) := by
  exact vge_natCast (v := v) n

theorem vge_intCast (n : ℤ) : Vge v 0 (n : K) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · simpa using vge_natCast (v := v) k
  · simpa using (vge_natCast (v := v) k).neg

/-- If `v(e) ≥ 1` then `v(1 + e) = 0`. -/
theorem val_one_add {e : K} (he : Vge v 1 e) : v (1 + e) = 0 := by
  rw [v.map_add_eq_of_lt_left, v.map_one]
  rw [v.map_one]
  exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℤ) < 1)) he

theorem one_add_ne_zero {e : K} (he : Vge v 1 e) : 1 + e ≠ 0 := by
  intro h
  have := val_one_add he
  rw [h, v.map_zero] at this
  exact WithTop.top_ne_coe this

/-- If `v(x) = n` and `v(y) ≥ n + 1`, then `v(x + y) = n`. -/
theorem val_add_eq {x y : K} {n : ℤ} (hx : v x = n) (hy : Vge v (n + 1) y) : v (x + y) = n := by
  rw [v.map_add_eq_of_lt_left, hx]
  rw [hx]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (lt_add_one n)) hy

theorem add_ne_zero_of_val {x y : K} {n : ℤ} (hx : v x = n) (hy : Vge v (n + 1) y) :
    x + y ≠ 0 := by
  intro h
  have := val_add_eq hx hy
  rw [h, v.map_zero] at this
  exact WithTop.top_ne_coe this

theorem val_mul_coe {x y : K} {m n : ℤ} (hx : v x = m) (hy : v y = n) : v (x * y) = (m + n : ℤ) := by
  rw [v.map_mul, hx, hy]; rfl

theorem val_pow_coe {x : K} {m : ℤ} (hx : v x = m) (k : ℕ) : v (x ^ k) = (k * m : ℤ) := by
  rw [v.map_pow, hx]
  rw [← WithTop.coe_nsmul, nsmul_eq_mul]

theorem val_zpow_coe {x : K} {m : ℤ} (hx : v x = m) (k : ℤ) : v (x ^ k) = (k * m : ℤ) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact val_pow_coe hx n
  · rw [zpow_neg, zpow_natCast, v.map_inv, val_pow_coe hx n]
    rw [show (-(n : ℤ) * m : ℤ) = -((n : ℤ) * m) by ring]; rfl

theorem val_inv_coe {x : K} {m : ℤ} (hx : v x = m) : v x⁻¹ = (-m : ℤ) := by
  rw [v.map_inv, hx]; rfl

theorem val_div_coe {x y : K} {m n : ℤ} (hx : v x = m) (hy : v y = n) : v (x / y) = (m - n : ℤ) := by
  rw [v.map_div, hx, hy]; rfl

end ZInQ.Mult
