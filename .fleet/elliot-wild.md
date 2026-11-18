# Wild inertia period: proved; semistable inertia input still open

`SZRaynaud.wildPeriodCoprime_proof : SZRaynaud.WildPeriodCoprime` is in
`ZInQKernel/Contrib/OneProof/WildPeriodCoprime.lean`. A point is fixed over a finite
subextension of the chosen algebraic closure. On its normal closure, averaging
wild displacements removes the `ℓ`-part of the order of the automorphism, since
`ℓ` is invertible at the base. This gives the prime-to-`ℓ` period without a
ramification group or pro-`p` input.

The core compiled on Lean 4.35.0, and the proof body passed against the exact
statement extracted from `SZRaynaud.lean`. Both checks report only `propext`,
`Classical.choice` and `Quot.sound`. The actual contribution import has not been
built: the copied cache lacks `SZRaynaud.olean` and thousands of its dependencies.

The row `elliotWildInertiaTrivial` now reduces to the existing
`ReductSplit.SemistableUnipotent` input alone. Its consumer only needs the
square-zero identity for wild inertia. The read Silverberg–Zarhin 3.5 gives
semistable reduction and supplies no inertia action. The next print to read is
Silverberg–Zarhin 3.3 (locator UNVERIFIED; the paper is cited); the older SGA 7
route needs a separate reading and strict henselization comparisons.

No row was removed and no leaf was added. H remains **24 strict / 24 strictest
GLUE**; the complete theorem, including pole completeness, remains **25 / 25**.
The manuscript check and projected counts for each print are in
`docs/research/elliot-wild.md`; the Lean checks are in `scratch/elliot-wild/log.md`.
