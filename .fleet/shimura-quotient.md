# Shimura quotient handoff

**Scoped result.** The rational intertwining comparison is closed.
`HeckeCompat` is equivalent to `ν ∘ t = x ∘ ν` in the genuine rational Hom
space, and every positive denominator for `x` gives the same test. This
bridge was committed separately.

The scheme-theoretic sum of the saturated annihilator images is now constructed
as an abelian subvariety. Given a genuine quotient by that sum,
`PrintQuotient` is equivalent to being isomorphic to the quotient map, with
the isomorphism commuting with the maps from `J`. A connected scheme kernel
implies `KerConnected`; the converse for surjections remains open.

**Known issue.** The recorded page read flags the conjugate-form misprint on
p. 526 before clause (iv), outside these clauses. No new manuscript error was
found. The connected-kernel comparison must retain the printed surjectivity
clause in the reverse direction.

**Verified.** The three new `ShimuraQuotient*.lean` modules compile, and the
standalone audits in `scratch/shimura-quotient/` report only `propext`,
`Classical.choice` and `Quot.sound` for all 18 theorems.

**Remaining glue.** `AbVarQuotientBySubvarietyExists` states the exact
representability target. The complement route requires generalizing the
finite stabilizer quotient to the complement's arbitrary finite subgroup and
descending the quotient map and its kernel square back to `J`. The reverse
kernel comparison then needs finiteness of the factor through the quotient by
`(ker ν)⁰`. The [report](../docs/research/shimura-quotient.md) records the Lean
statements, sizing and manuscript check.
