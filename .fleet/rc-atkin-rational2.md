# Rational Atkin–Lehner handoff

`rationalAtkin hQ` constructs the involution over ℚ for every exact
divisor on `X0Branch.model N`, the model of the at-scale parametrization.
It has the pinned complex chart action and squares to the identity.
The pullbacks of the two Laurent generators are `j(Qτ)` and
`j((N/Q)τ)`; the swap occurs only in the Fricke case.

`genericFibreAtScale` gives the original `BasedAtkinOnPoints` and the
translated formula at the normalized rational cusp, with the pinned
sign. The proof extends the generic point difference by the valuative
criterion, reads it at each field point using elliptic good reduction
over valuation rings containing ℚ, and descends the constant by density.
Rationality of the fixed scale remains an input.

`overRelationAtScale` and `overRelation_baseChange` give the morphism
form for integral specialization after identifying the generic models
and their point readings. The integral identifications, the
`BasedSpecialization` comparison, and the cuspidal multiplier and
weighted row remain separate. No printed leaf was added.

The guarded focused Lake build checked all ten modules. The 65 axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
See `docs/research/rc-atkin-rational.md` and
`scratch/rc-atkin-rational/log.md`.

Implementation SHA: `e88d31d166097ff2cb13627539fafbbccc1690fd`.
Final SHA: `git log -1 --format=%H -- .fleet/rc-atkin-rational2.md`
(the commit containing this handoff).
