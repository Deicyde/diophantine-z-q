# Prime traces on the standard model

**Scoped stop.** `R16Thm1.BShStandardModel` and `AfTateLam.HeckeJ1DS`
remain open. The complex calculation now compares both coordinates
from the same Vélu sums on each prime superlattice. It includes the
order-two kernel and the good-prime diamond, where scaling the periods
by `p` scales the mark to `p/N`. The lattice partition and the pointwise
identification of normalized division-polynomial roots are proved.

`BShTraces.exists_primeTrace_of_coordinate_germs` gives the exact
`IsPrimeTrace` from a finite Galois family of generic branch embeddings
with the matched germ comparison. It descends the product of the
Abel–Jacobi images, extends it to the curve and specializes the product
at the given `AtTau` points.

What remains is to construct that family over `ℚ(X)`. Show that the
normalized prime division polynomial splits in the meromorphic germ
fields, transport its cyclic kernels and the mark-disjointness test
through the splitting field embeddings, and compare the resulting
marked pairs in the same local permutation. The existing conditional
trace theorem and `bShStandardModel_of_primeTraces` then give the row.

The offline Lake build of `BShTraces` and its helpers passed. All 45
axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
No leaf or fold was added. The
[research report](../docs/research/bsh-traces.md) gives the exact scope,
the Lean statements, and the manuscript check.
