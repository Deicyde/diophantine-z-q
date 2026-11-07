# Implementation note: The main theorem

- `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck` (`ZInQKernel/Main.lean`)
  proves `FrozenTarget` from the four hypotheses and the named finite check
  `ZInQ.Compiler.Universal.HaltingNodeCheck` (item 1 of the halting-node-check article).
  `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.
- The four-hypothesis theorem `ZInQ.exists_bounded_integer_polynomial_defining_integers_of`
  keeps its `sorry` until the check has a kernel proof `h`. Its proof is then
  `exists_bounded_integer_polynomial_defining_integers_of_nodeCheck h hH hPC h22 hCAT`.
- Milestone 1 of KERNEL_PLAN.md checks the node statistics by `native_decide` in the separate
  library `ZInQFinite`, outside the audited root.
