# The printed 214 to 204 finite certificate

The Version 18 construction uses the route 214 → 212 → 204 → Conant's affine 200 → Conant's 198 → Brox's 196. The new certificate fills the first two links. The later links have their own reconstruction and printed-table checks. These are finite polynomial checks, not substitutes for the arithmetic soundness and completeness arguments.

Run from the repository root:

```sh
python -B scripts/test_v18_predecessor_transport.py
python -B scripts/check_v18_predecessor_transport.py --root . --report build/v18-predecessor-transport.json
```

The existing required **Construction regeneration and finite checks** job runs both commands and retains the full result in its artifact.

The checker parses the coordinate dictionary and all 188 equations in the manuscript section labelled `q214:rows`. It evaluates the displayed decimal coefficient chunks as integers and compares every coefficient, coordinate name and parent coordinate with the pinned `candidate214-ir.json`. It does not import or execute an upstream builder.

For 212 it constructs the eight replacement contact equations from the elementary symmetric functions of the five stated contact values, replaces the multiplicative aggregate with the additive aggregate, removes the two unused multiplication coordinates and their equations, and compacts the coordinate list. It retains the other 177 rows. Each of the resulting 186 equations is normalized to a primitive integer polynomial with positive first coefficient.

For 204 it applies the displayed powers of the nonzero scalar R to the retained coordinates. Each affected equation is divided by its least R power before normalization. It removes the two old square-root blocks, constructs the two reciprocal-pair blocks and their ratio equations over Q(sqrt(2)), and constructs the weighted aggregate from their recovered differences. It then compares all 186 equations and the retained coordinate map with the pinned 204 table. The report contains the complete intermediate 212 and reconstructed 204 rows, their original row numbers, the coordinate maps and the powers divided out.

The source formulas are in the supplied `quartic212_20261113_v25.tex` and `quartic204_20261114_v27.tex`, under `research/version18/198/upstream/H10-quartic198/source/papers/quartic_existence/`. The source214 hash is `b15d6477439c3e4be1e98723b69053244debce59e8715683c28fee82aa847ca4`; the target204 hash is `21da11b4a5c9f11d8a3253162283cbd339c0f35599ab9d578a2302009f725536`.

The checker does not read a separate212 table. It constructs and reports that intermediate, whose role in the chain is checked by the complete final204 equality. In a separate local comparison, all186 intermediate rows also matched Brox's historical212 table, SHA-256 `b2f32d64ef1fb2591d37cfd41aadf8869ce691c39ed92e0e597ec10aaa53fc75`. That additional comparison is not claimed as a CI input or assertion.

The additive aggregate is a changed arithmetic construction. This certificate does not assert that it follows from the old multiplicative aggregate by an invertible coordinate substitution. The Version 18 proof supplies the changed height argument. Likewise, division by R uses the proof that R is nonzero; the finite checker records the division but does not establish that arithmetic premise.

The negative tests change a small coefficient, a digit in a large coefficient, a coordinate name, a row number, and the supported coefficient syntax, and remove a row. All must be rejected. The full positive test checks the actual manuscript and both complete transport steps.
