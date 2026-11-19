# Equal dimensions make the Shimura quotient comparison finite

**Proved.** `ShimuraSteps.sameDimSurjectiveFinite` has exactly the existing
`SameDimSurjectiveFinite` type. The proof compares transcendence degrees at the
generic point, translates geometric kernel points into the finite generic fibre
after a field extension, and applies the existing finite-kernel criterion.
`ShimuraSteps.shimuraThm1Af_of_printed'` needs only the printed statement and
`ShimuraHeckeRelations`.

`ZInQKernel/Contrib/OneProof/SameDimFinite.lean` compiles with `lake env lean`.
The axiom scan covers both exported theorems and all nine private helpers; each
uses only `propext`, `Classical.choice` and `Quot.sound`. The focused
`#discharges` check matches the exact quotient row type. The candidate passes
`autofold.py --dry-run`: **5 LEAF / 24 GLUE → 6 LEAF / 24 GLUE** under both
strict and strictest. No fold was applied; the full assembly was not checked.

The composite Jacobian Hecke relations remain open GLUE. The recorded misprint on
Shimura p. 526 concerns the conjugate eigenform sentence outside the quotient
clauses. See [the report](../docs/research/samedim-finite.md) and
[the checks](../scratch/samedim-finite/).
