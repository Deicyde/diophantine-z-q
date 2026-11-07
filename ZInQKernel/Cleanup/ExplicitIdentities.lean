import ZInQKernel.Model.Field.CurveC
import ZInQKernel.Model.Field.SpecialPrimes
import ZInQKernel.Model.Field.Units
import ZInQKernel.Model.Heights.DuplicationForms

/-!
# Explicit identities in `K₀`

Blueprint: `model/field/explicit-identities.md`.

With `s² = 2`, `ε = 1 + s` (`epsilon`), `δ = 3 - s` (`delta`) and `d = 75 - 53 s` (`genD`),
the closed identities of items 1–5 hold (`k0_identities`); each `K₀` identity compares two
rational components. An element `u + v s` is totally positive exactly when `u > 0` and
`u² > 2 v²` (`K0.totallyPositive_iff`), so item 4 says that `d` and `δ` are totally positive,
that `ε` has sign vector `(+, -)` and that `σ±(δ) ∈ [1, 5]` (`embPlus_delta_mem`,
`embMinus_delta_mem` of `Model/Heights/DuplicationForms.lean`).
-/

namespace ZInQ

open QuadraticAlgebra K0

/-- `N(δ) = 7`. -/
theorem norm_delta : QuadraticAlgebra.norm delta = 7 := by
  rw [K0.norm_eq]; norm_num [delta]

/-- `N(s) = -2`. -/
theorem norm_sqrt2 : QuadraticAlgebra.norm sqrt2 = -2 := by
  rw [K0.norm_eq]; norm_num [sqrt2]

/-- `d ε⁴ = δ`, that is `(75 - 53 s)(17 + 12 s) = 3 - s`. -/
theorem genD_mul_epsilon_pow_four : genD * epsilon ^ 4 = delta := by
  rw [delta_eq_epsilon_pow_four_mul_genD, mul_comm]

/-- **Explicit identities in `K₀`** (items 1–5 of the article). -/
theorem k0_identities :
    -- 1.
    (genD ^ 2 = ⟨11243, -7950⟩ ∧ QuadraticAlgebra.norm genD = 7 ∧ (75 : ℤ) ^ 2 - 2 * 53 ^ 2 = 7) ∧
    -- 2.
    (epsilon * (sqrt2 - 1) = 1 ∧ epsilon ^ 2 = ⟨3, 2⟩ ∧ epsilon ^ 4 = ⟨17, 12⟩ ∧
      epsilon ^ 6 = ⟨99, 70⟩ ∧ QuadraticAlgebra.norm epsilon = -1) ∧
    -- 3.
    (genD * epsilon ^ 4 = delta ∧ (⟨75, -53⟩ * ⟨17, 12⟩ : K0) = ⟨3, -1⟩ ∧ delta ^ 2 = ⟨11, -6⟩ ∧
      QuadraticAlgebra.norm delta = 7 ∧ QuadraticAlgebra.norm sqrt2 = -2) ∧
    -- 4.
    ((0 : ℤ) < 75 ∧ (2 : ℤ) * 53 ^ 2 < 75 ^ 2 ∧ (0 : ℤ) < 3 ∧ (2 : ℤ) * 1 ^ 2 < 3 ^ 2 ∧
      (1 : ℤ) ^ 2 < 2 * 1 ^ 2 ∧ (2 : ℤ) ≤ 2 ^ 2) ∧
    -- 5.
    ((2 : ℤ) ^ 6 * 7 ^ 4 = 392 ^ 2 ∧ (392 : ℤ) ^ 2 = 153664 ∧ (7 : ℤ) ^ 2 < 392 ∧
      (676 : ℤ) = 26 ^ 2) := by
  refine ⟨⟨genD_sq, norm_genD, by norm_num⟩,
    ⟨epsilon_mul_sqrt2_sub_one, epsilon_sq, epsilon_pow_four, epsilon_pow_six, norm_epsilon⟩,
    ⟨genD_mul_epsilon_pow_four, ?_, delta_sq, norm_delta, norm_sqrt2⟩,
    by norm_num, by norm_num⟩
  ext <;> norm_num [K0.mk_mul_mk']

namespace K0

/-- `u + v s` is totally positive exactly when `u > 0` and `u² > 2 v²`. -/
theorem totallyPositive_iff (z : K0) : TotallyPositive z ↔ 0 < z.re ∧ 2 * z.im ^ 2 < z.re ^ 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  rw [TotallyPositive, embPlus_apply, embMinus_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have hu : (0 : ℝ) < z.re := by linarith
    have hn := mul_pos h1 h2
    refine ⟨by exact_mod_cast hu, ?_⟩
    have : (2 * (z.im : ℝ) ^ 2) < (z.re : ℝ) ^ 2 := by nlinarith
    exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (0 : ℝ) < z.re := by exact_mod_cast h1
    have h2' : 2 * (z.im : ℝ) ^ 2 < (z.re : ℝ) ^ 2 := by exact_mod_cast h2
    have hsq : ((z.im : ℝ) * Real.sqrt 2) ^ 2 < (z.re : ℝ) ^ 2 := by
      rw [mul_pow, hs]; linarith
    have := abs_lt_of_sq_lt_sq' hsq h1'.le
    constructor <;> linarith [this.1, this.2]

end K0

/-- The sign consequences of item 4: `d` and `δ` are totally positive, `ε` has sign vector
`(+, -)`, and `σ±(δ) ∈ [1, 5]`. -/
theorem k0_signs :
    TotallyPositive genD ∧ TotallyPositive delta ∧ signVector epsilon = (1, -1) ∧
      K0.embPlus delta ∈ Set.Icc (1 : ℝ) 5 ∧ K0.embMinus delta ∈ Set.Icc (1 : ℝ) 5 :=
  ⟨totallyPositive_genD, totallyPositive_delta, signVector_epsilon,
    Set.mem_Icc.mpr embPlus_delta_mem, Set.mem_Icc.mpr embMinus_delta_mem⟩

end ZInQ
