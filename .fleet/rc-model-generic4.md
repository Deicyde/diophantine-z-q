# rc-model-generic4

**Retired frozen fields: none yet.** No frozen field or count changes (hRC GLUE row, `docs/one-proof/OPEN.md`, section hRC (`docs/one-proof/OPEN.md#hrc`);
`PreLeaves.odd_staged`, `ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:305`, unchanged).

**Scoped stop.** Items 1 and 2 are proved; item 5 is partial; items 3 (W_Q) and 4 (good Hecke) are open.
`GenericFibreComparison` is not instantiated.

Compiles (13 new modules in `ZInQKernel/Contrib/OneProof/RC/ModelGeneric4/`, no sorry, no axiom
declaration, axioms only propext / Classical.choice / Quot.sound):
- Item 1: `rationalPoints_rationalPointAtParameter`. For every τ ∈ ℍ, the pinned class at the inverse
  evaluation is `analyticCyclicPair τ`, collisions included. Route (b): (b1)
  `pairQuotientJ_analyticCyclicPair` (Vélu quotient of the period curve has invariant j(Nτ), at every level;
  new order-two function-field map `twoFFHom`); (b2) `rationalPoints_rationalPointAtParameter_of_transcendental`;
  (b3) `dense_transcendental_analyticJ`; (b4) `continuous_rationalPointAtParameter` and `continuous_markedLift`.
- Item 2: `exists_complexPoint_eq` (every complex point of `branchFiniteOverQ N` is `complexPoint N τ`), via
  `exists_analyticCyclicPair_eq` (coprime lift to SL₂(ℤ), lattice homothety, j-surjectivity).
- Item 5 (partial): actual readings `levelPairClass` and `branchPairClass` (the latter does not depend on the
  chosen parameter), and `pairClass_conjunct` for `e = rationalOpenIsoOverQ h₂`.

Remains (statements in the report): item 3 needs the lattice image of `E[Q] + C` under a seam map of the
actual Vélu composite, plus the point formula of the variable-change function-field isomorphism; then
agreement with `rationalAtkin hQ` at every point (items 1–2) and by density on the open. Item 4 needs the
branch double-coset multiset (lift to chart points, τ-independence via `complexPoint_eq_iff`) and the
index-p lattice comparison. No leaf proposed; no error verdict.

Report: `docs/research/rc-model-generic4.md`. Log: `scratch/rc-model-generic4/log.md`.
Final SHA: the commit that adds this file (its parent is b66514600).
