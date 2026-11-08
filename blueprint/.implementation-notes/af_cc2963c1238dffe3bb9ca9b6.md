# Implementation note: Partial sums of χ(n)/n approximate L(1,χ)

- Owner: pp-lseries (plan step 1). Namespace `ZInQ.Progressions`; modules import Mathlib (and earlier `Progressions` modules) only.
- Lean name: `ZInQ.Progressions.norm_partialSum_sub_LFunction_one_le`.
- Draft:
  ```lean
  variable {q : ℕ} [NeZero q]
  theorem norm_partialSum_sub_LFunction_one_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
      {x : ℝ} (hx : 1 ≤ x) :
      ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n / (n : ℂ) - χ.LFunction 1‖ ≤ 2 * q / x
  ```
- Mathlib: upstream `norm_LFunction_sub_sum_le` for `σ > 1`, then `le_of_tendsto` as `σ → 1⁺` using continuity of `χ.LFunction` (`differentiable_LFunction`) and of `σ ↦ (n : ℂ) ^ (σ : ℂ)` (`continuous_ofReal.const_cpow`); `Nat.lt_floor_add_one`.
- The proof gives `q / x`; the article states the plan's `2q/x`, which is what the twisted sum bound uses.
