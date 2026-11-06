# Implementation note: Size of the program literal

- Lean names: `ZInQ.Compiler.Universal.c3 := code wrapper` (`@[irreducible]`),
  `c3_lt : c3 < 2^20000000`, `c3_gt : 1399 < c3`, `wrapper_small`.
- FINITE COMPUTATION. Decidable form:
  ```lean
  theorem wrapper_small : 3 ≤ wrapper.length ∧ wrapper.length < 2^18 ∧
      ∀ ins ∈ wrapper, ins.maxField < 2^18 := ...
  ```
  `wrapper.length` is about $1.5\times10^5$ if the Lean precision program is as large as the
  manuscript's; evaluating the lowering in the kernel is then too slow for `decide`. Prove
  instead structural size bounds: `(IR.code s start aux).1.length = IR.size s` with
  `IR.size` a small recursive function on the IR syntax, evaluated by `decide` on the IR
  term (hundreds of statements), and similarly `IR.maxReg s`. Then `code_lt` gives
  `c3 < 2^(18*(4*len+1)+1) < 2^20000000` by `Nat.pow_lt_pow_right` and `omega`; `code_ge`
  gives `c3 > 1399`.
- Mathlib: `Nat.pow_lt_pow_right`, `Nat.pow_le_pow_right`.
- Upstream reuse: none.
- Difficulty: medium (the structural size function).
