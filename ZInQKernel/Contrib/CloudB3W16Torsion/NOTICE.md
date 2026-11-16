# Worker16 torsion source port

**Verification status:** source assembly only. No H102 discharge is claimed until
all imported modules, the leaf, and the exact Main/Discharges scratch compile.

## Immutable sources

- anthropics/fermats-last-theorem, `6e837e75355538c7f80bab5b956861e86c4eacc2`.
  Complete upstream LICENSE, NOTICE, and ATTRIBUTION.md are preserved in
  `Vendor/AnthropicFLT/{LICENSE,NOTICE.upstream,ATTRIBUTION.upstream.md}`.
- AxiomMath/Stacks, `c496df0d9beea9deaeabcea8492605f9a0a2313b`, was assessed as an
  alternative. Its complete `AbelianTorsion/FromCube` proof has a much larger
  dependency cone (over 10,000 additional modules). No Stacks geometric code is
  copied into this family.
- Existing FLT ports under CloudW02Connectedness and CloudB2X0Transitive are reused
  by import, not duplicated. The independent finite-group port is imported from
  CloudB3W16FiniteGroup, not copied or replaced here.

## Exact source route

`GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero`
counts the torsion of a proper smooth connected group scheme with relative dimension
g over an algebraically closed field. Its source proof includes the degree formula
`endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero`: multiplication by n has degree
n^(2g). That formula uses the theorem of the cube, a symmetric ample line bundle,
and an Euler-characteristic/degree calculation; it is not an additional hypothesis.

`RelativeBridges.lean` translates the exact PkgI2 field, structure map, law and Krull
dimension to those source definitions. `NativeBridges.lean` separately records
multiplication étale and finite, finiteness of torsion, and the comparison with the
additive torsion subgroup. Finiteness alone is explicitly not treated as the
cardinality formula.

## Port changes

- Local import paths moved below this contribution; original declaration namespaces retained.
- Nonessential broad negative-instance/simp preambles and reactivation scaffolding removed.
- Namespace/open/export commands expanded to ordinary Lean commands; metadata aliases
  resolved directly. No new elaborators, macros, syntax or notation introduced.
- Source-local notation expanded as literal expressions at its lexical scope.
- Backward elaboration transparency restored for the fixed Lean4.35/Mathlib56a00585
  environment. Definitions and theorem conclusions are not weakened.
- The six large curve modules are assigned to the independent Worker16 curve lane,
  which splits them between whole proof declarations and preserves their original
  public solution APIs. They are not authored or duplicated in this lane.

`Vendor/AnthropicFLT/SOURCE_MANIFEST.json` records original source hashes, paths,
relocated names, direct reused imports and the six delegated original modules.
All authored Lean files are under 150KB after scaffold removal. A lexical audit is
not compilation evidence.
