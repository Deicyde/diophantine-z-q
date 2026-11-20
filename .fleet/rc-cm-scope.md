# CM field scope

**Verified:** `CMScope/Field.lean` narrows the source statement to one
imaginary quadratic field split at 2N, with the two exceptional fields
excluded, the conductor prime to 2N times the field discriminant, and
the proper Heegner lattice pair at a fixed level orientation. The broad
statement implies it, including on both level-one models.
`CMScope/Orientation.lean` specializes the scope to an eligible form.
At general level the scoped statement is still an input.

**Scope finding:** the two old Heegner anchor conclusions ask for every
positive conductor prime to N times the field discriminant. Tex 2841
includes 2. The drafted wrappers preserve those old conclusions and ask
explicitly for 2 to divide the newform level; the original anchor does
not provide that proof. The genus and ring-class selectors already
supply the needed coprimality. The prior citation mismatch at tex 1784
and 1788 does not affect this CM evaluation.

**Verification stop:** both source modules passed serial
`lake env lean -j1` under the 60 GB cap. Host load rose to 220.01
(limit 120) and the next check stalled on disk I/O. The consumer
wrappers and axiom audits are unverified. To resume, use the
[scratch patch and checks](../scratch/rc-cm-scope/log.md) after the
resource gate clears. The [report](../docs/research/rc-cm-scope.md)
records all call sites and remaining inputs.

Final Lean, report, and scratch commit:
`9c1df2283ffaad8bcbf6f48593dcd224d6c2149a`.
