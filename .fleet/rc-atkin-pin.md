# Atkin–Lehner sign handoff

The (O.7) theta stage, the special-fibre sign, and the remaining `aθ`
coefficient reading now use the integer unit of the actual newform
eigenvalue at `p ^ N.factorization p`. The existing modularity and
least-level comparison identifies the newform with the consumer's
cusp form.

The signed translation of the scaled Eichler integral is proved in
`ℂ`, modulo periods, and in the elliptic point group. It holds for the
rational parametrization from the at-scale join on the model's interior
complex chart, where the Atkin–Lehner involution is constructed.

The scoped stop for (a) is the rational model comparison:
construct `RationalAtkin` on `X0Branch.model` and descend the chart
identity to `BasedAtkinOnPoints` at the rational cusp. The adapters
then give the rational translation, `π(W∞)` under the normalization
`π(∞) = 0`. For (b), `BasedSpecialization` names the two comparisons
of reduced based differences with the coarse divisor classes.
Additivity proves the exact pinned `SpecialFibreAtSigns` quotient
equation from these inputs. The integral model and the per-row
reduction comparison remain with good reduction.

All six modules passed serial `lake build`; all 22 axiom checks list
only `propext`, `Classical.choice`, and `Quot.sound`. The inherited
Milne citation scope and Jetchev–Kane level-one issue are recorded in
[the report](../docs/research/rc-atkin-pin.md). No new printed leaf
was added.

Final proof and report commit: `07bf69805e211887f974fe148638ebd3b4c0e02f`.
The final branch SHA includes this handoff and can be read with
`git log -1 --format=%H -- .fleet/rc-atkin-pin.md`.
