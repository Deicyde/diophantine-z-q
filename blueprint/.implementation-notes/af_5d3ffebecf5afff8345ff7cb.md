# Implementation note: The compiled circuit of a register machine

- Lean name: `ZInQ.Compiler.Packed.compiled_natRel_iff`.
- Draft:
  ```lean
  theorem compiled_natRel_iff (p : RM.Program) (r k : ℕ) (hp : p.Valid r) (hk : 1 ≤ k ∧ k ≤ r)
      (a : Fin k → ℕ) :
      (compiled p r k).natRel Formula.powerTemplate a ↔ p.Accepts r a
  ```
- Proof: `dag_natRel_iff`, the macro semantics lemmas, `sound`, `complete`.
- Upstream reuse: none.
- FINITE COMPUTATION: no. Difficulty: medium (glue, ≈80 lines).
