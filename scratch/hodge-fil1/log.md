# Results log

- VERIFIED: audited `dcc3d7723` against the live `frozenTarget` signature. The previous pairing supplier needs Picard representability and Picard-zero properness, both absent from that signature. The dimension-free Hodge–Tate decomposition, comparison bounds, T10 and rank `2g` are available on the right objects.
- VERIFIED: the manuscript invokes an uncited Hodge number at L10996; the Scholze corrigendum is cited. No new error identified.
- VERIFIED: autofold count preview exits 0, strict and strictest both 5 LEAF / 26 GLUE before and after, 31 H rows. The preview names a missing provider and is not a fold.
- SPECULATIVE: adapt the native stabilizer quotient and descended normalized family to obtain compatible perfect Weil pairings, avoiding full Picard representability.
- VERIFIED: `lake env lean` checks the contribution. `#print axioms` for both rank proofs and both assemblers reports only `propext`, `Classical.choice` and `Quot.sound`; see `axioms.txt`.
- VERIFIED: `lake env lean scratch/hodge-fil1/Dependencies.lean` passes. The pointwise proof has no dependency on the original row or its clause-3 consumers. Both assembler proof bodies pass after inspecting generated instance proofs for scalar multiplication and the surface numeral.
