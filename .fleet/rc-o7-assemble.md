# Actual (O.7) stage assembly

Scoped stop. `O7Assemble.datumAt` constructs the actual row from the
selected datum, the full odd filter, the local chart and realization
inputs, the fixed stage geometry, and the pointwise CM readings. It uses
one Picard orbit map for the weights, normalizers and reference reduction.
The row uses `ThetaClose.actualPmLocal`, `PMAdelic.geometry`, and
`StageKummer.Setup.ev`. The actual family wrappers give
`Odd.ThetaComparison` and `OddStagedInstance` from these rows and the
independent reading of the fixed `W.aθ`.

Three readings remain open in this join: `OrbitRead` for the specified
class idele in the based double quotient; its reduced norm valuation
against the ideal norm; and the concrete `StageKummer.ArtinMatch`
projection from the checked ideal sign comparison. The two pointwise CM
identities and the actual selector values remain with their existing
owners. The report lists the inherited fixed inputs and explains why
each remaining premise is narrower than (O.7).

All new Lean modules compile separately. The 70 axiom checks found only
`propext`, `Classical.choice`, and `Quot.sound`. No wiring was edited and
no print was added. The inherited source audit records that the cited
Jetchev–Kane result at tex 8468–8474 does not cover level one.

Report: `docs/research/rc-o7-assemble.md`. Final implementation and report
SHA: `ba14c46b123da917e2ab6ffbd146d4828a1b1770`.
