# Implementation note: The universal interpreter at the program literal

- Lean name: `ZInQ.Machine.uAccepts_c3_iff`.
- Draft:
  ```lean
  theorem uAccepts_c3_iff (x : ℕ) : UAccepts c3 x ↔ acceptsNaturals (decode5Fin x)
  theorem uAccepts_c3_encode5_iff (c : Fin 5 → ℕ) :
      UAccepts c3 (CantorDecoder.encode5 (c 0) (c 1) (c 2) (c 3) (c 4)) ↔ acceptsNaturals c
  ```
- Proof: `uAccepts_iff`, `decodedHalts_code_iff`, `wrapper_halts_iff`, `lower_halts_iff`,
  `precisionStmt_correct`, `decode5_encode5`. Never unfolds `c3`.
- This is the statement the natural chapter needs to prove (C.4) together with its packed
  compiler theorem for `universalInterpreter` and `specialization_iff`.
- Mathlib: none. Upstream reuse: `ZInQ.CantorDecoder.decode5_encode5`.
- FINITE COMPUTATION: no.
- Difficulty: low (~40 lines).

Shared design (machine notes): namespace `ZInQ.Machine`, files under
`ZInQKernel/Compiler/Machine/`. Primitive programs as `Array Instr`, configurations
`ℕ × (ℕ →₀ ℕ)` or `ℕ × List ℕ`, one-step function `step : Prog → Config → Option Config`
so that Mathlib's `StateTransition.eval`/`Reaches`/`Respects`/`tr_eval`
(Mathlib/Computability/StateTransition.lean) give runs and simulations. Large programs (the
interpreter, the precision machine, the wrapper) are Lean terms built by functions; their
codes, in particular `c_3`, are never evaluated by any proof.
