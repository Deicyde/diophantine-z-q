# Appendix F stages

Built the Appendix F detecting stages. A uniform product of eight finite-field
counts clears torsion over degree-at-most-four fields and gives the exact common
multiple on the conductor-one genus point. The genuine division cocycle yields a
fixed detector and primes in its joint Galois field. The same detector works for
every finite prime exclusion. The sequence supplies `PreDataSpec` and
`stages_advance`; the reduced-curve Kummer map has the required algebra,
including the row on finite torsion.

The scoped stop is `WitnessSpecialization`: on the fixed multiplied witness,
identify the `StageKummer` evaluation with the finite row of the squared
Frobenius cocycle at the same place, in `ZMod (2 ^ M)`. Local reduction is already
available; the place, Frobenius and split-twist comparison remain. The conditional
proof of `WitnessValuation` on `lamOf` compiles. No manuscript error was found.

All 20 Lean files were checked separately with `lake env lean`. Their theorem
axiom checks use only `propext`, `Classical.choice` and `Quot.sound`. See
`docs/research/rc-stages.md` for the exact identity and manuscript check, and
`scratch/rc-stages/log.md` for the proof and compile log.

Final proof and report SHA: `3f19ccd1a99c9ac51c6f61445e36d22affa02db7`.
This note is the only change in the following handoff commit.
