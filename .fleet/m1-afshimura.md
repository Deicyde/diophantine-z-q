# AfShimura

`AfTateLam.afShimura_proof : AfTateLam.AfShimura` is unconditional. It constructs
the abelian variety quotient and extends the descended Hecke action to the
coefficient field. The six quotient modules and the proof module built.
The live bundle field type check passed. The 46 audited theorems use only
`propext`, `Classical.choice` and `Quot.sound`.
[Report](../docs/research/m1-afshimura.md)

The fold can remove `shimuraThm1Af` from the live NOS route and reduce the
open-row count from 24 to 23. The existing `bShStandardModel` wiring and
Shimura 1973 reading stay in use. [Fold specification](../docs/research/m1-afshimura.md#fold-specification)

The prior source audit records a missing conjugation subscript in Shimura
1973, p. 526. The local comment at `R16Thm1.lean:53` also describes as weaker
an intertwining relation that is equivalent here.
[Known issues](../docs/research/m1-afshimura.md#known-issues)
