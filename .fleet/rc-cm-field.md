# CM field descent handoff

**Scoped stop.** `PreparedParam.CMFieldOfDefinition (X0Branch.model N)`
remains open. The tree proves Tau Ceti's ring class field, its arithmetic
Artin equivalence with the Picard group, and the idelic lattice comparison.
It does not prove that \(j\) of each proper ideal class lies in that field.
The archived `MainTheoremCMj` assumes precisely that comparison and its Artin
action (strict GLUE, unread). The existing idelic fallback uses Shimura 1971.
The CCL audit checks the trace theorem; its separate field-of-definition
locator remains unverified.

The immediate arithmetic input is simultaneous singular-modulus membership
in one complex embedding of \(H_O\). There is also a branch comparison:
the forms \([2,1,1]\) and \([2,-1,1]\) have the same two \(j\)-values at
level two but give distinct points of the normalization. The branch from
the chosen \(N\)-orientation must be shown to descend.

[Report](../docs/research/rc-cm-field.md) · [Results log](../scratch/rc-cm-field/log.md).
No new Lean files, declarations or prints; no new compilation or axiom audit.
The existing model and prepared-value adapters are unchanged.

Scout commit: `8f59a98e2ef5e40bf5064e36dfefafffc5b50fd5`.
The final handoff commit's SHA is given by
`git log -1 --format=%H -- .fleet/rc-cm-field.md`. A commit cannot record
its own SHA literally in a file it contains without changing that SHA.
