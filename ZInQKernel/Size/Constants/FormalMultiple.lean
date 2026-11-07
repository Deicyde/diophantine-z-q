import ZInQKernel.Size.Constants.Catalogue

/-!
# Size of the formal multiple constant

Blueprint: `size/constants/formal-multiple-size.md`.

The existence of a successful formal multiple (`size/formal-multiple/formal-multiple-existence.md`)
gives `1 ≤ M₀ ≤ N_s^10`; with `N_s < 2^(2^2054)` this gives `c_* = 4 M₀ < 2^(2^2059)`.
-/

namespace ZInQ.Size

open Syntax

/-- A successful formal multiple exists below `N^10` (blueprint
`size/formal-multiple/formal-multiple-existence.md`). This is the input proved by the
formal-multiple section; its statement is final and its proof is supplied there. -/
theorem exists_formalCondition_le_pow_ten {N : ℕ} (hN : 1 ≤ N) :
    ∃ m, 1 ≤ m ∧ m ≤ N ^ 10 ∧ FormalCondition N m := by
  sorry

/-- `1 ≤ LFM(N) ≤ N^10`, and `LFM(N)` is a successful index, for every `N ≥ 1`. -/
theorem leastFormalMultiple_bounds {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ leastFormalMultiple N ∧ leastFormalMultiple N ≤ N ^ 10 ∧
      FormalCondition N (leastFormalMultiple N) := by
  obtain ⟨m, hm1, hm, hc⟩ := exists_formalCondition_le_pow_ten hN
  obtain ⟨h1, h2, h3⟩ := leastFormalMultiple_spec ⟨m, hm1, hc⟩
  exact ⟨h1, (h3 m hm1 hc).trans hm, h2⟩

/-- `1 ≤ M₀ ≤ N_s^10` and `M₀` is a successful index. Only `N_s ≥ 1` is used, which holds
without the catalogue bound (`Syntax.Ns_pos`, from Dirichlet's theorem). -/
theorem M0_bounds : 1 ≤ M0 ∧ M0 ≤ Ns ^ 10 ∧ FormalCondition Ns M0 := by
  rw [M0_eq]; exact leastFormalMultiple_bounds Ns_pos

set_option exponentiation.threshold 2100 in
/-- The estimate for `c_*`, for variables. -/
theorem four_mul_lt_of {m n : ℕ} (hm : m ≤ n ^ 10) (hn : n < 2 ^ 2 ^ 2054) :
    4 * m < 2 ^ 2 ^ 2059 := by
  have he : 2 + 2 ^ 2054 * 10 < 2 ^ 2059 := by
    rw [Nat.mul_comm]; exact closed_comparisons_2
  calc 4 * m ≤ 4 * n ^ 10 := Nat.mul_le_mul_left 4 hm
    _ < 4 * (2 ^ 2 ^ 2054) ^ 10 :=
        Nat.mul_lt_mul_of_pos_left (npow_lt_npow_left hn (by decide)) (by decide)
    _ = 2 ^ 2 * (2 ^ 2 ^ 2054) ^ 10 :=
        congrArg (· * (2 ^ 2 ^ 2054) ^ 10) (by norm_num : (4 : ℕ) = 2 ^ 2)
    _ = 2 ^ 2 * 2 ^ (2 ^ 2054 * 10) := by rw [← npow_mul]
    _ = 2 ^ (2 + 2 ^ 2054 * 10) := (npow_add _ _ _).symm
    _ < 2 ^ 2 ^ 2059 := npow_lt_npow_right (by decide) he

/-- `c_* < 2^(2^2059)`. -/
theorem cstar_lt (hCAT : CatalogueBound) : cstar < 2 ^ 2 ^ 2059 := by
  rw [cstar_eq]; exact four_mul_lt_of M0_bounds.2.1 (Ns_bounds hCAT).2

/-- Size of the formal multiple constant (the blueprint statement). -/
theorem formal_multiple_size (hCAT : CatalogueBound) :
    1 ≤ M0 ∧ M0 ≤ Ns ^ 10 ∧ cstar < 2 ^ 2 ^ 2059 :=
  ⟨M0_bounds.1, M0_bounds.2.1, cstar_lt hCAT⟩

end ZInQ.Size
