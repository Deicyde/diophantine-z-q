# Abelian variety quotient: results log

- VERIFIED (source): the previous stabilizer quotient takes a very ample line bundle and seesaw input. The underlying scheme theorem already handles finite locally free equivalence relations with affine orbit coverage.
- VERIFIED (source): the Poincaré complement theorem returns an addition isogeny; its complement map is not required to be a closed immersion. The kernel identity component is supplied by `L3.covAbVar` and `L3.covHom`.
- VERIFIED (Lean): `AbVarQuotientFinite.lean` compiles. `finiteSubgroupQuotient_exists` gives an isogeny quotient by every finite closed subgroup scheme over ℚ, with an actual kernel square and unique descent for homomorphisms killing the subgroup. `FiniteAxioms.lean` prints only the three standard axioms for all seven theorems.
- VERIFIED (Lean): `AbVarQuotientComplement.lean` compiles. `abVarQuotientBySubvarietyExists` uses the finite quotient of the scheme intersection with the complement and descends the map and kernel property along the addition isogeny. `ComplementAxioms.lean` prints only the three standard axioms for all four theorems.
