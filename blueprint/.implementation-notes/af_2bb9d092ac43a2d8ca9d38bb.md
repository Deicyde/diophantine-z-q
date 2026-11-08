# Implementation note: A lower bound for |L(1,χ)| at every nonprincipal character

- Owner: pp-final. Namespace `ZInQ.Progressions`; modules under `ZInQKernel/Progressions/`, importing Mathlib and the delivered `Progressions` modules only.
- This article replaces the earlier "uniform bound for twisted sums" (`2^24 q^5`). The delivered count `twentytwo_primes_of_LFunction_lower_bound` (Mertens/Unconditional) takes a lower bound `c ≤ ‖L(1,χ)‖` for all `χ ≠ 1` directly and forms `B = ((log q + 3)^2 + 6q)/c` itself, so no separate twisted-sum bound is needed. The name `norm_twistedSum_le` is already taken (by `‖S_χ(x)‖ ≤ (M² + 6q)/‖L(1,χ)‖`).
- Lean name: proposed `ZInQ.Progressions.norm_LFunction_one_ge_min`.
- Draft:
  ```lean
  variable {q : ℕ} [NeZero q]
  theorem norm_LFunction_one_ge_min {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
      min (1 / (256 * (Real.log q + 3) ^ 7)) (1 / (40 * (q : ℝ) ^ ((3 : ℝ) / 2))) ≤
        ‖DirichletCharacter.LFunction χ 1‖
  ```
  (If the real-character bound is stated with `q * Real.sqrt q`, use the same spelling here.)
- Inputs: `norm_LFunction_one_ge_of_sq_ne_one` (delivered, LSeries/ComplexChar) and `norm_LFunction_one_ge_of_sq_eq_one` (pp-final, real characters); `min_le_left`, `min_le_right`, case split on `χ ^ 2 = 1`.
