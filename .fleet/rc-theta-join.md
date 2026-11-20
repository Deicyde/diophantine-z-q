**Scoped stop.** `ThetaJoin.levelPmLocal` assembles the actual Schwartz
product, finite norm spheres, adelic norm character, phase, and
trace-zero frames for the explicit level order. `levelStage` and
`levelValLift` apply the existing consumers to this construction. The
construction still requires the indexed neighbour transport, so there
is no unconditional inhabitant of `PMLocal`.

Each of the 15 Lean files compiles with `lake env lean`. The scratch
audit checks all 105 theorems and 16 definitions; every entry reports
only `propext`, `Classical.choice`, and `Quot.sound`.

To finish the neighbour transport, align each line's adelic generator
with the frame chart, compare its double coset with the indexed
neighbour, and match the mod p² lattice test to its local membership.
The good-prime norm character follows from reduced norm valuation one,
which the chosen generator must supply. ELLIOT supplies the (O.3) root
choices and discriminant data; the geometry and evaluation remain with
`rc-pm-geometry`.

The late support bridge needs the manuscript's odd filter. With
`ell₀=3`, `h_*=-7`, `D=N=193`, and `x=i+15j+15ij`, the affine
generator can lie in a class order while the level weight at 193
vanishes. The report gives the counterexample. For the filtered support
statement, the rational intersection and good-prime tests are proved;
the exceptional-place tests remain with this task's follow-up.

Implementation and report commit: `1dd0b63e00eb7f0cc52907162d36ac424b7c804d`.
See `docs/research/rc-theta-join.md` for the exact hypotheses and the
manuscript check.
