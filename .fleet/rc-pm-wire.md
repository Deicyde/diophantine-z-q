# (O.7) pinned integral row handoff

`PMWire.oddStagedOfGoodRows` fills the existing
`Wiring.PreLeaves.odd_staged` at `SelectorTotal.withParamIndices a`.
The special values come from the Néron extension of the fixed rational
parametrization. The integral Atkin–Lehner operator is the unique extension
of the pinned rational involution, and the signed relation uses its actual
newform eigenvalue. The generic comparison extends the ordered function
field comparison on the smooth proper compactification and restricts to
the generic source; it works for either model design.

The integral row has no cusp section. The translation is the reduction
of the rational elliptic point obtained from the moved infinity cusp.
The represented `J₀(N)` and its geometric cusp classes supply the inputs
to the existing Elkik print. The legacy divisor interface uses formal
labels for zero and the target translations. Its values on actual coarse
points are still the readings of the same Néron extension.

All eight Lean modules and the scratch `#discharges` check built
serially. All 77 axiom checks returned only `propext`, `Classical.choice`,
and `Quot.sound`. The constructor and the quotient predecessor each have
30 binders; the new row and relation inputs are narrower.

Still needed: construct the good modular model and identify its ordered
chart and residue actions, supply the good Hecke branch and eigenvalue
comparison, and identify the actual conductor-one CM orbit and lifts.
The existing Elkik proposition, the choice of the fixed multiplier and
the theta coefficient comparison remain inputs. The rationality witness
for the scale is still supplied in `a.hr`. See
`docs/research/rc-pm-wire.md` for the theorem roadmap and
`scratch/rc-pm-wire/log.md` for the audit.

Implementation and report SHA: `37d72e7677ae4e62184bc35915a07964503792a8`.
The final handoff SHA is the result of
`git log -1 --format=%H -- .fleet/rc-pm-wire.md`; a commit cannot contain
its own literal hash.
