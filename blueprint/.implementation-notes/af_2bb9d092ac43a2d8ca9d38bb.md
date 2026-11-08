# Implementation note: A uniform bound for twisted sums

- Owner: pp-mertens (plan step 4.2, once steps 2 and 3 land) or the final assembly task. Namespace `ZInQ.Progressions`; modules import Mathlib (and earlier `Progressions` modules) only.
- Lean name: proposed `ZInQ.Progressions.norm_twistedSum_le`.
- Draft:
  ```lean
  variable {q : ℕ} [NeZero q]
  open ArithmeticFunction in
  theorem norm_twistedSum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
      ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n * Λ n / n‖ ≤ 2 ^ 24 * (q : ℝ) ^ 5
  ```
- Mathlib: `Real.log_le_sub_one_of_pos` at `√q` (so `log q + 3 ≤ 3 √q`), `Real.sq_sqrt`, `pow_le_pow_left₀`, `div_le_iff₀`; inputs `norm_LFunction_one_mul_twistedSum_le`, `norm_LFunction_one_ge_of_sq_ne_one`, `norm_LFunction_one_ge_of_sq_eq_one`.
- The plan has `C₁ q^(5/2)`; the cleaner `2^24 q^5` (via `M ≤ 3√q`) avoids bounding `(log q + 3)^7 / q^(3/2)` and still leaves the final instance far below `2^(q^8)`.
