import ZInQKernel.Model.Field

/-!
# An exact square test in `K₀`

Blueprint: `model/heights/square-test.md`.

For `u, v ∈ ℚ`, `Sq(u, v)` holds if there are a sign `η ∈ {1, -1}` and rationals `t, y₀` with
`t² = u² - 2v²` and `y₀² = (u + η t)/2`, such that either `y₀ ≠ 0` and
`(y₀ + (v / 2y₀) s)² = u + v s`, or `y₀ = 0`, `v = 0` and `u/2 = y₁²` for some `y₁ ∈ ℚ`.
Then `u + v s` is a square in `K₀` iff `Sq(u, v)`.
-/

namespace ZInQ

/-- The square test `Sq(u, v)`. -/
def SqTest (u v : ℚ) : Prop :=
  ∃ η : ℚ, (η = 1 ∨ η = -1) ∧ ∃ t y₀ : ℚ, t ^ 2 = u ^ 2 - 2 * v ^ 2 ∧ y₀ ^ 2 = (u + η * t) / 2 ∧
    ((y₀ ≠ 0 ∧ (⟨y₀, v / (2 * y₀)⟩ : K0) ^ 2 = ⟨u, v⟩) ∨
      (y₀ = 0 ∧ v = 0 ∧ ∃ y₁ : ℚ, u / 2 = y₁ ^ 2))

theorem K0.mk_sq (a b : ℚ) : (⟨a, b⟩ : K0) ^ 2 = ⟨a ^ 2 + 2 * b ^ 2, 2 * a * b⟩ := by
  rw [pow_two, K0.mk_mul_mk']; ext <;> simp <;> ring

/-- **The exact square test**: `u + v s` is a square in `K₀` iff `Sq(u, v)`
(including the case `u + v s = 0`). -/
theorem isSquare_iff_sqTest (u v : ℚ) : IsSquare (⟨u, v⟩ : K0) ↔ SqTest u v := by
  constructor
  · rintro ⟨r, hr⟩
    have hr' : (⟨u, v⟩ : K0) = ⟨r.re, r.im⟩ ^ 2 := by rw [hr, pow_two]
    rw [K0.mk_sq] at hr'
    have hu : u = r.re ^ 2 + 2 * r.im ^ 2 := congrArg QuadraticAlgebra.re hr'
    have hv : v = 2 * r.re * r.im := congrArg QuadraticAlgebra.im hr'
    set y₀ := r.re
    set y₁ := r.im
    set w := y₀ ^ 2 - 2 * y₁ ^ 2
    obtain ⟨η, hη, hηw⟩ : ∃ η : ℚ, (η = 1 ∨ η = -1) ∧ η * |w| = w := by
      rcases le_or_gt 0 w with h | h
      · exact ⟨1, Or.inl rfl, by rw [one_mul, abs_of_nonneg h]⟩
      · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
    refine ⟨η, hη, |w|, y₀, ?_, ?_, ?_⟩
    · rw [sq_abs, hu, hv]; ring
    · rw [hηw, hu]; ring
    · by_cases hy : y₀ = 0
      · right
        refine ⟨hy, by rw [hv, hy]; ring, y₁, by rw [hu, hy]; ring⟩
      · left
        refine ⟨hy, ?_⟩
        have : v / (2 * y₀) = y₁ := by rw [hv]; field_simp
        rw [this, hr', K0.mk_sq]
  · rintro ⟨η, -, t, y₀, -, -, ⟨-, h⟩ | ⟨-, hv, y₁, hy₁⟩⟩
    · exact ⟨_, by rw [← h, pow_two]⟩
    · refine ⟨⟨0, y₁⟩, ?_⟩
      rw [← pow_two, K0.mk_sq, hv]
      ext <;> simp
      linarith

end ZInQ
