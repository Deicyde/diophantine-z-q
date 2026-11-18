# Appendix F witness specialization

**Proved.** `actualWitness` in
`ZInQKernel/Contrib/OneProof/RC/WitnessSpec/Specialize.lean` constructs the
unchanged `StageKummer` at the selected conductor-one datum and proves
both `WitnessSpecialization` and `WitnessValuation` ((O.2)). The equality
holds in `ZMod (2 ^ M)` before the integer lift, with the fixed row and
no sign or unit correction.

The construction uses the prime exhibiting `selectedFrobenius` for
every reduction. It identifies the geometric level torsion, specializes
the split twist using the same root, and descends the ring class point
through the quadratic residue field at the contracted principal inert
prime. The global multiplied witness and the prior stage data are inputs.
The total interface is filled by zero off the selected datum; no geometric
evaluation on those entries, theta forms, or (O.7) is supplied.

All 18 Lean files compile individually in the Lake environment. Their
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
No mathematical error was found in the scoped manuscript lines. The theorem
statements and manuscript check are in
`docs/research/rc-witness-spec.md`; results are in
`scratch/rc-witness-spec/log.md`.

Final proof and report SHA: `a08c7a156dbb8d14e4d9e383ac900ed465ce7523`. This handoff is committed separately.
