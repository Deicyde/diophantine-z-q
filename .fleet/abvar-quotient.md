# Abelian variety quotient handoff

**Proved.** `ShimuraSteps.Quotient.abVarQuotientBySubvarietyExists` constructs
the genuine quotient by any abelian subvariety over ℚ. It has the actual
scheme kernel square and the universal property for abelian variety
homomorphisms. The proof quotients a Poincaré complement by its finite
intersection with the subvariety, then descends along the addition isogeny.
The finite quotient applies to arbitrary finite closed subgroup schemes.

The genuine quotient by the saturated annihilator image sum now exists
unconditionally, and `PrintQuotient` characterizes its map up to a commuting
isomorphism. `KerConnected` is equivalent to connectedness of the scheme
kernel for surjective homomorphisms; the reverse direction retains the
printed surjectivity hypothesis.

**Verified.** All four `AbVarQuotient*.lean` modules and the four standalone
axiom audits compile. All 18 theorem audits report only `propext`,
`Classical.choice` and `Quot.sound`. There is no remaining quotient or
connected kernel glue from this task.

**Known issue.** The prior source audit records a conjugate-form misprint on
p. 526 of Shimura 1973 before clause (iv). It does not affect these clauses.
No new manuscript error was found. The
[report](../docs/research/abvar-quotient.md) records the statements and the
manuscript check.
