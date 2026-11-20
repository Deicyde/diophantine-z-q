# CM field descent handoff

The Lean target ranges over more orders and levels than tex 2915–2916, which
uses the split setting of tex 2839–2844 and fixed orientations across
conductors. The work found no counterexample to the broader target.

Both arithmetic stages are proved. Every proper ideal singular modulus
is an algebraic integer of degree at most the proper class number.
`singularModulusMemRingClass` puts all these values in one embedding of
the ring class field over the prescribed quadratic embedding, using
Kronecker's congruence at split primes and Chebotarev. The oriented ideal
product puts both Heegner plane coordinates in that same field.

`cmFieldOfDefinition_modelOne` and `cmFieldOfDefinition_one` close level
one. At general level `cmFieldOfDefinition` needs only `BranchDescends N`:
the values of a fixed finite family of regular sections at the chosen
branch must land in the embedded field. The existing forward ratio for
`j(Nτ)` does not express those sections in the plane coordinates.
Lean checks the discriminant −7 example: equal plane pairs, distinct
normalized points, and reflected parameters.

All 29 modules and the statement check pass `lake env lean` with only
the three standard axioms. No entry point or integration row changed.
See the [report](../docs/research/rc-cm-field-2.md),
[statements](../scratch/rc-cm-field-2/statements.txt), and
[axiom audit](../scratch/rc-cm-field-2/axioms.txt).
