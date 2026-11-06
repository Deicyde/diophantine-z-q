# Two explicit integer comparisons (height-comparisons)

- Lean name: `ZInQ.height_comparisons`.
- Decidable statement:
  ```lean
  theorem height_comparisons : 41^3 * 676 * 392^36 < 9^108 ∧ 392 < 41^3 := by decide
  ```
  and the real corollaries via `Real.log_lt_log`, `Real.log_pow`, `Real.log_mul`.
- FINITE COMPUTATION: yes. Size: numbers of about 104 decimal digits. Method: `decide` reduces
  `Nat.ble` with GMP-accelerated kernel arithmetic (instant); `norm_num` also works. No
  `native_decide` needed.
- Difficulty: easy.
