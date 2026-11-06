# Implementation note: Cantor pairing and unpairing

- Lean names: reuse upstream `ZInQ.CantorDecoder.pair`, `loop`, `decode`, `encode5`, `decode5`
  and theorems `pair_inj`, `decode_pair`, `pair_decode`, `pair_loop`, `decode5_encode5`,
  `encode5_decode5`, `pairing_equation_iff` (lean/ZInQ/CantorDecoder.lean, sorry-free). New:
  `ZInQ.Machine.pairing_chain_iff` for item 5.
- Draft (new):
  ```lean
  theorem pairing_chain_iff (c : Fin 5 → ℕ) (t : Fin 4 → ℕ) :
      (∀ i : Fin 4, 2 * (t i : ℤ) - ((c i + T (i+1)) * (c i + T (i+1) + 1) + 2 * T (i+1)) = 0) ↔
      t 0 = CantorDecoder.encode5 (c 0) (c 1) (c 2) (c 3) (c 4) ∧ t 1 = .. ∧ t 2 = .. ∧ t 3 = ..
  -- where T k = if k = 4 then c 4 else t k
  ```
  by four applications of `pairing_equation_iff` (note its integer form
  `2t - (a+b)(a+b+1) - 2b = 0`, a rearrangement of the article's form).
- Mathlib's `Nat.pair` is a different (Szudzik-type) pairing and is not used.
- FINITE COMPUTATION: no.
- Difficulty: trivial (~40 lines new).

Shared design (machine notes): namespace `ZInQ.Machine`, files under
`ZInQKernel/Compiler/Machine/`. Primitive programs as `Array Instr`, configurations
`ℕ × (ℕ →₀ ℕ)` or `ℕ × List ℕ`, one-step function `step : Prog → Config → Option Config`
so that Mathlib's `StateTransition.eval`/`Reaches`/`Respects`/`tr_eval`
(Mathlib/Computability/StateTransition.lean) give runs and simulations. Large programs (the
interpreter, the precision machine, the wrapper) are Lean terms built by functions; their
codes, in particular `c_3`, are never evaluated by any proof.
