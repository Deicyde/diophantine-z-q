# Results log

- Base: c2a92cd2c8e857dbe6e456a40917102aa9e8b02d.
- Reuse: RC13 genus partner and witness selection; shared GenusOdd witness/nonzero point, with comparison mod torsion rather than a single common multiplier; Odd detector algebra; absolute Frobenius density and torsion-field congruence; vendored prime-to-residue-characteristic specialization.
- Build cache: first dependency attempt failed at unchanged PoleManuscript due to stale Pole olean. Serial rebuild with revision-based invalidation started.
- Typing gap: Odd.lambda_frobenius_sign asks for a row on all geometric points, while the finite detector needs it only on the torsion.
- Compiled with serial `lake env lean -j1`: `SequenceCore.lean` and `Kummer.lean`. All printed dependencies are subsets of propext, Classical.choice and Quot.sound.
- `stageSequence`: recursively excludes previous primes at precision `cw+1+i`; `stageTest_one`: Legendre test accepts 1.
- `divisionTower`: compatible divisions of Q; `DivisionTower.divides`: finite-level multiple; `DivisionTower.coe_proj_cocycle`: finite component is the difference of the two division points; `DivisionTower.isCocycle`, `restriction`, `detectingElement`: cocycle, homomorphism on the Tate kernel, fixed square evaluation of any selected translation. `finiteRow` and `finiteRow_proj`: reduction of the integral row factors through the torsion quotient.
