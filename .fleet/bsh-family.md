# Generic prime branches on the fixed standard model

`BShFamily.bShStandardModel_proof` proves the exact
`R16Thm1.BShStandardModel` GLUE row, and `BShFamily.heckeJ1DS_proof`
proves `AfTateLam.HeckeJ1DS`. No leaf or fold was added.

The normalized prime division polynomial splits in the meromorphic germ
field at every parameter. Its finite Galois splitting field supplies
the weighted multiset of nonzero x-coordinates in each cyclic kernel.
The mark test removes exactly the horizontal kernel when the prime
divides the level. A lift into each germ field identifies the surviving
kernels with the allowed analytic branches. The same bijection matches
both Vélu coordinates, including the diamond on the good-prime
horizontal branch. The short sums and field embeddings commute with
the Galois action, giving the prime trace on the prescribed model.

The offline Lake build and the focused `#discharges` check passed.
All 74 new theorem scans use only `propext`, `Classical.choice`, and
`Quot.sound`; the row has no remaining assumptions. The initial
prerequisite build breached the single-process rule and was stopped.
Subsequent checks used an exclusive compiler lock.

No proof step remains for this row. The repository's fold and review
remain separate. The [research report](../docs/research/bsh-family.md)
records the provenance, Lean statements, discharge output, and manuscript
check; the bridge is in neither the manuscript nor its citations.
