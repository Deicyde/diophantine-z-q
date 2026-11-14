# Source-bound Frobenius components for C10

These optional sources package existing Frobenius mathematics for the original
native `PkgI3.AbVar` interfaces. They are **not an unconditional proof of C10,
H, the frozen integer-defining polynomial theorem, or Hilbert10**.

## Source and dependency contract

The native object layer used for the checks is
`ZInQKernel/HDecomp/Objects.lean` from Deicyde fork revision
`8ec807114805afd96d90c468ec2cf40c6f9cc634`, Git blob
`2f4e4818392ffd810b3aaad227f71228febcedd3`, SHA-256
`bf2519646471349e64f5e3069a69c6946ed8f3a7bbfb34123e681b8d581ba6f3`.
The original object file is not replaced by this contribution.

The exact compiler and existing dependency caches are:

- Lean 4.35.0: `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`;
- Stacks: `c496df0d9beea9deaeabcea8492605f9a0a2313b`.

A different canonical Objects snapshot has its own source binding. Equal
constructor regions do not make entire QM leaf packages equivalent or establish
a combined canonical kernel check. This source branch must not be merged into a
different object/dependency setup on the strength of the local compilation alone.

## Components and boundaries

- `C10Frobenius.lean`: relative Frobenius as an actual group map into the
  canonical twist, with exact underlying map and naturality.
- `C10PrimeField.lean`: canonical twist specialization and actual group
  endomorphism over `ZMod p`.
- `C10FiniteField.lean`: the q-power endomorphism where `q = #k = p^f`, not
  an arbitrary p-power k-linear map over a general characteristic-p field.
- `C10FieldPoints.lean`: exact arithmetic-Frobenius action and point-group
  automorphism over perfect extensions of the finite field.
- `C10TorsionAction.lean`: that same-field action restricted to each actual
  n-torsion set, not a characteristic-zero reduction map.
- `C10FrobeniusGeometry.lean`: universal homeomorphism and scheme surjectivity;
  finiteness retains local finite type, supplied by properness for proper groups.
- `C10AbVarFrobenius.lean`: original native Hom to the canonical twist, retaining
  proper/smooth/geometrically integral structure and the original isogeny predicate.
- `C10AbVarFiniteField.lean`: q-power Frobenius in the original native End ring,
  with the exact geometric map and finite-surjective isogeny predicate.
- `C10AbVarPointAction.lean`: original native point and Tate maps identified
  with the existing arithmetic-Galois action of the finite field, including the
  same-variety coefficient-prime 3/5 case.

Each has a separate `Check*.lean` probe (the general adapter uses `Check.lean`).
The original native point/Tate/Galois definitions are reused, not replaced by a
new point model, inverse-limit transport, or basis/free/rank construction.

## Checks and reproduction

`SOURCE-MANIFEST.json` records exact source/probe checksums. The scoped checks
compile all nine implementation modules to oleans, import them into the nine
probes, and check their exact declaration reports. All 61 named implementation
reports use only `propext`, `Classical.choice`, and `Quot.sound`; the action probe
also audits its proved coefficient-prime-five fixture.

Use already populated, checksum-verified caches at the pins above. Do not
cold-build Mathlib or Stacks. The supplied direct compiler guard accepts explicit
cache paths and an explicit package root; it never invokes dependency resolution.
First compile the unmodified pinned native Objects source under its native module
name into a separate output directory. Compile these modules beside their probes,
with that output directory in the search path, and then compile the probes.

The public checking scripts are runtime guards and software controls, not new
proof evidence by themselves. Full default-root/candidate CI and independent
source acceptance remain separate from these scoped module and axiom checks.
Do not add default imports, change dependency pins, or relax an audit to make an
optional component pass.

## Remaining actual C10 join

C10 still needs the genuine shared fields, varieties, conjugate, isogenies,
reduction maps, and nonzero N for both coefficient primes 3 and 5, with the three
original commuting squares and all trace/coefficient/continuity/semisimplicity
hypotheses. The arithmetic element here belongs to the finite field's absolute
Galois group, not GQ. No global `IsFrobAt` element or characteristic-zero reduction
comparison is constructed.

The later rational EndTrace pairing is a separate, explicitly source-only
application until it has its own canonical import, type/body, and destination
validation. It is not an integer-polynomial independence-of-ell theorem and is
not included in this checked proof snapshot. Preserve the earlier frozen
integration snapshots rather than silently extending an in-flight review.

AI-assisted implementation and verification used Metamate/Agentcloud. The
scope and remaining hypotheses above are part of the contribution, not omitted
from its completion claim.
