# Implementation note: The packed-history construction

- Lean name: `ZInQ.Compiler.Packed.construction (p : RM.Program) (r k : ℕ) : NatM Formula`
  and `ZInQ.Compiler.Packed.compiled (p) (r k) : Syntax.NatCircuit`.
- Draft: a transcription of `compileRegisterMachine` in
  `construction/integer-diophantine-compiler.js` (hierarchical mode): allocate
  `q c K B T F D`, `R j`, `N j`, `S i`; build the list of conjuncts in the order of the article;
  sub-branch variables `V i, W i` are allocated inside the pass over the program, after the
  register formulas. Incoming sums: `incoming[x.nonzero]` is extended before
  `incoming[x.zero]`.
- Mathlib: `List.foldl`, `List.filterMap`.
- Upstream reuse: none.
- FINITE COMPUTATION: no. Difficulty: medium (≈150 lines). Validity of the program
  (`RM.Program.Valid p r`) is a hypothesis of the semantic theorems, not of the definition.
