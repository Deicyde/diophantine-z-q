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
- Status: items 1 and 2 are proved in general (`ZInQ.Compiler.Natural.toCircuit_item1`,
  `toCircuit_natRel_iff`, with `toCircuit_wellScoped` and `toCircuit_poly`), under explicit scope
  hypotheses (valid node encoding, the scope invariant `Pres`, private call blocks). Item 3 is proved
  only for the packed construction (`ZInQ.Compiler.Packed.packed_spec`, `compiled_natRel_iff`); the
  general statement needs a formal notion of "the macros of a construction". Record the article once
  item 3 is general, or narrow item 3 to the constructions the chapter uses.
