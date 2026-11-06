# Implementation note: Circuits of hierarchical constructions

- Lean names: `ZInQ.Compiler.Formula.dag_poly_eq_kappa`, `dag_wellScoped`,
  `dag_natRel_iff`.
- Draft:
  ```lean
  theorem dag_natRel_iff (prog : NatM Formula) (k : ℕ) (h : ArgsBelowProg prog) (c : Fin k → ℕ) :
      (toCircuit prog k).natRel powerTemplate c ↔ (prog.run' (init k)).HoldsSome (extend c)
  ```
- Proof: invariant of the hash-consing interpreter (each node id denotes its expression),
  as in the syntax chapter's `builder-soundness`; then `exists_call_iff` and
  `powerTemplate_natRel`.
- Mathlib: `List.getElem_append`, `MvPolynomial.aeval_bind₁` (or `eval₂Hom_bind₁`).
- Upstream reuse: none.
- FINITE COMPUTATION: no. Difficulty: medium-hard (hash-consing invariant ≈250 lines; can
  be shared with the syntax chapter's construction theorem if both use one `Prog`).
