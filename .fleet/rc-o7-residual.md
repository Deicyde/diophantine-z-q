# Actual (O.7) residual

`datumAtActual` constructs the actual row using the completed local torus
chart and realizations, the orbit reading on normalized class ideles,
the reduced norm valuation, and the Artin character match. Its remaining
proof inputs are the selector value, the two pointwise CM identities,
and the fixed Atkin signs and cusp annihilation, with the existing
stage data. `oddStagedActual` builds the rows at `D.toNat` and returns
`Nonempty (OddStagedInstance W)` for `PreLeaves.odd_staged`, using the
existing fixed-coefficient reading, torsion bound and odd-sign input.

All seven Lean modules compile. The audit of 23 declarations uses only
`propext`, `Classical.choice` and `Quot.sound`. No new prints or wiring
changes. See [the report](../docs/research/rc-o7-residual.md) for statements,
owners and the manuscript check.

Tex 8209–8217 and 9265–9279 use the reference CM point on every admissible
row; tex 9439–9443 explicitly includes torsion rows. The fixed Lean
selector still needs `∀ i D, W.admissible i D → (I.selG D).isSome`.
The inherited source audit records that the Jetchev–Kane citation at
tex 8468–8474 does not cover level one.

Final implementation and report SHA: `27d81c0572d4bf4a56b640e48d51d4bca22d6529`.
