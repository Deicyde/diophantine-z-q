# Shared Atkin–Lehner sign for (O.7)

`AtkinSign.oddStagedActual` gives `Nonempty (OddStagedInstance W)`
without a separate `hSign`. `SpecialFibreAtSigns … w` fixes the
geometry's sign to the theta stage's `w`, so the old constructor's
equality holds by `rfl`. The previous special-fibre and (O.7)
constructors are reused. An old fibre with `hSign` on the level
primes also gives the new input.

The remaining Atkin statement is ELLIOT, tex 8487–8489: on each coarse
supersingular point, the elliptic quotient of the degree-zero divisor
`[W x] - [W infinity]` is `(w p : ℤ)` times the quotient of
`[x] - [infinity]`. The analytic sign of the newform exists in the
tree; the bridge to the specialized rational parametrization is still
geometric input. The row still uses the cusp annihilation and point
identities, and the odd instance still needs the independent coefficient
reading, torsion bound, and odd root-number input.

`Geometry` and `Family` passed serial `lake build` checks. All six
audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. No new prints. The inherited Jetchev–Kane source audit
records the omission of level one from the citation at tex 8468–8474;
the source locators are UNVERIFIED here.

See [the report](../docs/research/rc-atkin-sign.md) for the precise
statements and manuscript check.

Final implementation and report SHA: `20ca79fca8150d1b5448ab49d8b4e76f891f5667`.
The handoff commit SHA is available with
`git log -1 --format=%H -- .fleet/rc-atkin-sign.md`.
