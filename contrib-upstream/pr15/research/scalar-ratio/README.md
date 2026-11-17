# Raw common-strict scalar-ratio milestone

This packet derives cofactor coordinates from the actual common-strict matrices,
cycles and closed rows, then proves an integral-unit equivalence including zero
functionals. Its boundary–cup adapter uses those same rows. Actual arithmetic
tensor compatibility remains **OPEN**; this is a conditional connecting theorem.

## Start here

- Mathematical review: [derivation](DERIVATION.md), [precise contract](CONTRACT.md)
  and [verification status](VERIFICATION.md).
- Formal sources: [Coordinate](../../lean/Research/DerivativeSwitch/Coordinate.lean),
  [CommonStrict](../../lean/Research/DerivativeSwitch/CommonStrict.lean),
  [UnitCriterion](../../lean/Research/DerivativeSwitch/UnitCriterion.lean) and
  [BoundaryCup](../../lean/Research/DerivativeSwitch/BoundaryCup.lean).
- Cloud runner: [repository handoff](../../OPENMATH.md) and
  [frozen verification project](verification/README.md).
- Arithmetic consumer: [uninstantiated arithmetic contract](inputs/ARITHMETIC_CONTRACT.md).

The new 18 selected declarations extend the preserved
[21-target packet](../boundary-scalar/README.md), which includes the original six.
The new combined cloud inventory therefore has **39 targets**. Neither earlier
freeze is rewritten; the accepted manuscript and dependency pins are unchanged.

The uploaded ZIP and pasted handoff are retained unchanged under `inputs/`.
[Provenance](PROVENANCE.json) separates the supplier's uncompiled candidates
from current native evidence. The supplied finite tests reuse the preceding
matrix utilities; they are useful controls, not an independent checker.

Run local native verification with pinned installed dependencies:

```sh
python3 -B research/scalar-ratio/verify.py --output lean/.checks/scalar-ratio-fresh
```

Outputs must be new. The driver invokes no paranoid checker and dispatches no
cloud job. It checks prior frozen inputs, compiles all seven combined solution
modules, inspects the 39 selected types/axioms, and runs the exact controls.
Use the source-only preparation command in OPENMATH.md for the later cloud run.
