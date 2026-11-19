# Fowler uniqueness handoff

**VERIFIED — ready for the integrator's LEAF review.** Two quadratic orders of equal trace
discriminant are isomorphic as rings, and ring isomorphism preserves their proper class number.
The proofs also give the lattice formula `O = ℤ + f·𝓞 k`, recovery of the field discriminant and
conductor index, and the description of the fraction field as `ℚ(√Δ)`.

`FowlerProp27PrintCanonical` uses the proper class number of the explicit order of discriminant
`Δ` as a function of `Δ`, matching Fowler's definition on p. 613. Lean proves it equivalent to
`FowlerProp27Print`. Both new modules compile. The axiom audit found only `propext`,
`Classical.choice`, and `Quot.sound`. The live `#discharges` scan matches
`fowlerProp27_of_canonical` to `OpenResearchLeaves66.fowlerProp27` with only the canonical
statement assumed.

The read-only autofold preview moves one GLUE to LEAF: both strict and strictest go from
4 LEAF / 25 GLUE to 5 LEAF / 24 GLUE on 29 rows. No fold was applied. The next step is the
integrator's row replacement; the published proposition itself remains the single input.
No new manuscript or source error was found.

[Research report](../docs/research/fowler-unique.md) ·
[Discharge](../scratch/fowler-unique/discharges-output.txt) ·
[Dry run](../scratch/fowler-unique/autofold-output.txt)
