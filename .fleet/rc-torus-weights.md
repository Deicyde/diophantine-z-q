# Actual (O.7) torus weights

`datumWeights` supplies the `DatumAt.weights` field for the actual stage
on the full odd filter, given the adelic realization of the orientation
fibers and the local weight readings. On each orbit, the fixed rational
translation of the right ideal yields one right order unit. Its norm
character multiplies the norm factor and its inverse multiplies the
Schwartz factor. The torus norm character equals the descended ideal
character on the class of the same finite idele. Both base orders follow
from the local values. No point values or sums are used.

`Norm.lean` and `Actual.lean` compile separately with `lake env lean`.
All eight new theorems and the three listed definitions use only
`propext`, `Classical.choice` and `Quot.sound`, or subsets of those.
No printed leaf was added.

The remaining integration inputs are the actual Picard-fiber presentation
and normalized ideal representatives, the equality of local reduced-norm
valuations with the prime exponents of the ideal norm, and the readings of
the supplied `PMLocal` fields against the finite norm and Schwartz factors.
The constructor takes the matching quadratic basis and the descent for
`D > 1`; it uses the existing trivial descent for `D = 1`.

Known issue: the bare adelic norm character need not descend through
right order units. The two transported factors cancel as required for the
combined summand in tex 8571–8578 and 8612–8614.

Report: `docs/research/rc-torus-weights.md`.
Verified work and report commit: `43893ad246808c048f873de422cbc1fcfcebf61b`.
