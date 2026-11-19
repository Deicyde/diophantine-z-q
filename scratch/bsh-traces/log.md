# Results

- Base: `5ec952f7e`.
- `BShTraces.weierstrassP_cosets`, `BShTraces.G_cosets`: finite coset identities for the dot-period lattice series. Initial offline module build passed; standard axioms only.
- Vendor check: `eval_jLattice_eq_zero_of_isAddCyclic` identifies a root of the modular polynomial; `fibrePoly_j_eq_prod_veluQuotient_j` factors the polynomial into odd-prime quotient j-invariants; `exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed` gives a point map. None supplies the matched marked Weber coordinate over a meromorphic field.
- `AtTau` is a punctured-limit test. The possible different pointwise definitions of Weber at exceptional lattice invariants must be removed by working in germs.
- `short_coefficients_of_cosets`, `short_mark_of_cosets`: short coefficients and marked x-coordinate from the same finite coset sums.
- `short_pair_weights`, `short_two_weights`: vendored odd-pair weights and order-two coefficients; the double pole term vanishes at order two.
- `triangular_coordinates`, `horizontal_coordinates`: matched j and Weber coordinates on the prime lattice branches; horizontal correction scales the mark to `p/N`.
- `triangular_mark_order`, `horizontal_mark_order`: vanishing of `k/N` in the two target lattices is equivalent to `N ∣ k` and `N ∣ pk`, respectively.
- `prime_torsion_lattice_unique`, `normalized_torsion_roots`: unique lattice branch for a nonzero prime class; pointwise identification of all normalized division-polynomial roots.
- `fieldGerm_coordinates`, `generic_j_ne`, `exists_ringHom_of_pair_relations`: identification of coordinate germs, exclusion of the two exceptional generic values, and the passage from matching pair relations to a field embedding.
- `exists_extension_of_permuted_branches`, `specialize_sum_of_branches`, `exists_branch_lift_of_stalk_values`: Galois descent, extension, and specialization through one valuation.
- `exists_primeTrace_of_branch_germs`, `exists_primeTrace_of_coordinate_germs`: exact `IsPrimeTrace` under the common finite Galois family with the specified germ comparisons.
- `lake --offline --no-cache --log-level=info build +ZInQKernel.Contrib.OneProof.BShTraces`: passed, 11384 jobs.
- Axiom scan: 45 output records, each with `propext`, `Classical.choice`, `Quot.sound`.
- Open: one finite Galois family of generic matched marked quotients and its local embeddings and permutations. No `#discharges` result.
