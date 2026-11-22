# Modifications to the vendored HodgeConjecture files

Source: `Paul-Lez/HodgeConjecture` @ `2ead713179628a3c738197d5996f51c8a9c886ac`, Apache-2.0,
"The Formal Conjectures Authors". See `../NOTICE` and `../LICENSE`.

Applied to every file under `Port/`:

* a provenance header naming the source revision and source path;
* module names `HodgeConjecture.A.B` remapped to
  `ZInQKernel.Contrib.CloudB3W17Hodge.Port.A.B`.

No statement or proof was changed by either of those.

## Files changed beyond the mechanical remapping

### `Port/Definitions/AlgebraicGeometry/ProjectiveSpace.lean`

The contribution rules forbid new notation in delivered modules. This file declared three:

| deleted | replaced at each use by |
|---|---|
| `local notation "ℤ[" n "]" => homogeneousSubmodule n ℤ` | — (unused once the next row is expanded) |
| `local notation3 "ℤ[" n "].{" u "," v "}" => homogeneousSubmodule n (ULift.{max u v} ℤ)` | `homogeneousSubmodule n (ULift.{max u v} ℤ)` |
| `scoped [AlgebraicGeometry] notation "ℙ("n"; "S")" => ProjectiveSpace n S` | `ProjectiveSpace n S` |

Seven use sites were expanded (`ProjectiveSpace`, `instIsProperProjTerminalFrom`, `toBase`,
`toBaseProper`, `Presentation.immersion`). The docstring that belonged to the deleted `ℙ(n; S)`
notation became a plain comment. Docstrings elsewhere keep the readable `ℤ[…]` and `ℙ(…)` forms,
since they are prose.

No statement, no proof term and no declaration name is otherwise changed; the module builds and
every declaration downstream of it is unaffected.

### Attempted and reverted

Removing `ProjectiveSpace.lean` from the port altogether was tried first, since no declaration of
it is referenced on the manifold path. It fails: `ComplexPoint/Basic.lean` and
`Lemmas/.../ComplexPoint/Basic.lean` depend on it for transitive Mathlib imports
(`Mathlib.AlgebraicGeometry.Stalk`, `…ResidueField`: `SpecToEquivOfLocalRing`,
`stalkClosedPointTo_comp`, `Scheme.residueField`, `SpecToEquivOfField`). Replacing those by direct
imports would mean editing more ported files, not fewer, so the narrower notation strip above was
preferred.
