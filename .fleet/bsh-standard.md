# Standard-model Hecke bridge

**Scoped stop.** The prime Hecke trace is still open, so neither
`R16Thm1.BShStandardModel` nor the identical `AfTateLam.HeckeJ1DS`
is discharged. The missing input is the comparison of marked cyclic
quotients over the generic function field with both Weber coordinates
of the triangular branches. The known quotient j-invariants do not
specify the images of the level point.

`BShStandard.exists_diamonds` proves the exact `IsDiamond` action for
every unit on every model in the row. The proof computes the transformed
Weber coordinate by division polynomials, transports its punctured germ
values to the model, extends the generic map, and uses the Albanese
property. Generic extension into a proper target and finite Galois
descent of points are also proved. Once the prime trace maps are
constructed and specialized, `bShStandardModel_of_primeTraces`
supplies the unchanged row.

The offline Lake build succeeded for all four new modules. All 30 axiom
checks report only `propext`, `Classical.choice`, and `Quot.sound`.
No leaf or fold was added. The [research report](../docs/research/bsh-standard.md)
lists the statements, the missing comparison, and the manuscript check.
