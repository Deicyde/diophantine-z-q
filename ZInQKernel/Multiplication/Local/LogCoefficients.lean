import ZInQKernel.Model.Field

/-!
# The coefficients of the truncated logarithm

Blueprint: `multiplication/local/logarithm-coefficients.md`.

The formal logarithm of `E` is `Σ_j (-1)^j binom(2j, j) d^{2j} T^{4j+1} / (4j + 1)`
(`logarithm-series.md`). Its coefficients `logCoeff j = (-1)^j binom(2j, j) / (4j + 1)` times
`16575` are the integers `c_0, …, c_6 = 16575, -6630, 11050, -25500, 68250, -198900, 612612`
for `j ≤ 6`, so the polynomial `L(z) = Σ_{j ≤ 6} c_j δ^j z^{4j+1}` (`δ = d²`) of the
truncated-logarithm template is `16575` times the degree-`25` truncation of the logarithm.

`truncLog δ z` is `L(z)` with `δ` in place of `d²`, over any commutative ring; the template
writes `d^{2j}` as `δ^j` with `δ = d² = 11243 - 7950 s`.
-/

namespace ZInQ.Mult

open Finset

/-- The coefficient `(-1)^j binom(2j, j) / (4j + 1)` of `d^{2j} T^{4j+1}` in the formal
logarithm of `E`. -/
def logCoeff (j : ℕ) : ℚ := (-1) ^ j * (Nat.centralBinom j : ℚ) / (4 * j + 1)

/-- The integer coefficients `c_0, …, c_6` of the truncated logarithm `L`. -/
def log25Coeff : ℕ → ℤ
  | 0 => 16575
  | 1 => -6630
  | 2 => 11050
  | 3 => -25500
  | 4 => 68250
  | 5 => -198900
  | 6 => 612612
  | _ => 0

theorem centralBinom_values :
    (List.range 7).map Nat.centralBinom = [1, 2, 6, 20, 70, 252, 924] := by decide

/-- **The coefficients of the truncated logarithm**: `16575 · (-1)^j binom(2j, j)/(4j+1) = c_j`
for `j = 0, …, 6`. -/
theorem log25_coefficients : ∀ j < 7, (16575 : ℚ) * logCoeff j = log25Coeff j := by
  have h := centralBinom_values
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  intro j hj
  interval_cases j <;> simp [logCoeff, log25Coeff, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

/-- The coefficient list, as in the template. -/
theorem log25Coeff_list :
    (List.range 7).map log25Coeff = [16575, -6630, 11050, -25500, 68250, -198900, 612612] :=
  rfl

/-- `16575 = 3 · 5² · 13 · 17`. -/
theorem sixteen575_factor : (16575 : ℕ) = 3 * 5 ^ 2 * 13 * 17 := by norm_num

/-- The truncated logarithm `L(z) = Σ_{j ≤ 6} c_j δ^j z^{4j+1}`, with `δ` standing for `d²`. -/
def truncLog {R : Type*} [CommRing R] (δ z : R) : R :=
  ∑ j ∈ range 7, (log25Coeff j : R) * δ ^ j * z ^ (4 * j + 1)

theorem truncLog_eq {R : Type*} [CommRing R] (δ z : R) :
    truncLog δ z = 16575 * z - 6630 * δ * z ^ 5 + 11050 * δ ^ 2 * z ^ 9 - 25500 * δ ^ 3 * z ^ 13 +
      68250 * δ ^ 4 * z ^ 17 - 198900 * δ ^ 5 * z ^ 21 + 612612 * δ ^ 6 * z ^ 25 := by
  simp [truncLog, sum_range_succ, log25Coeff]
  ring

/-- **`L` is `16575` times the degree-`25` truncation of the formal logarithm**:
`L(z) = 16575 Σ_{j ≤ 6} (-1)^j binom(2j, j) d^{2j} z^{4j+1} / (4j + 1)` with `δ = d²`, over any
field of characteristic zero. -/
theorem truncLog_eq_trunc {F : Type*} [Field F] [CharZero F] (d z : F) :
    truncLog (d ^ 2) z = 16575 * ∑ j ∈ range 7, (logCoeff j : F) * d ^ (2 * j) * z ^ (4 * j + 1) := by
  rw [truncLog, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have := log25_coefficients j (mem_range.mp hj)
  rw [← pow_mul, ← mul_assoc, ← mul_assoc]
  congr 2
  exact_mod_cast this.symm

end ZInQ.Mult
