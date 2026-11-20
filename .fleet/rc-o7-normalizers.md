The two normalizer permutations act on the actual weighted support orbits.
The split normalizer at each exact level prime power flips its orientation
bit, acts on the ideal class by Atkin–Lehner, and multiplies the combined
weight by the geometry's Atkin–Lehner sign. The division uniformizer flips
the last bit, acts by the geometry's uniformizer, and preserves the combined
weight. At every other prime the local generator stays fixed.

`O7Normalizers.normalizers` fills `DatumAt.moves` on the actual
`ThetaClose.actualPmLocal` and `PMAdelic.geometry` stage.
`ofPicardFibers` takes the independent Picard fiber equivalences directly.
The fixed level signs can be chosen by `geometrySigns`; the cusp field
follows from the divisibility into `L` of an annihilator of the reduced
cusp translations.

All six Lean modules compile individually. The axiom audit of 81
theorems and 41 other declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. No new printed leaves are used.

The remaining data and their owners are listed in
`docs/research/rc-o7-normalizers.md`. The independent torus weights and
reference reduction are still needed for (O.7). The report records the
inherited level-one citation scope issue at tex 8468–8474 and the use of
the corrected filtered support.

Verified result commit: `95005ee8244119ac4136fbf4139f14bd55e9f5db`.
This handoff is the final commit on top of that result.
