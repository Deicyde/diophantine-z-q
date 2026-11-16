# Native preflight checks (not proof compilation)

Fixed Lean 4.35.0, restored-main source base
`2dc949d688c407e32823c4e751679d66b2f40e65` (same tree as initial `0e70c94e`).
Run on the parent-approved shared host for **small availability checks only**.
All Lean processes were serialized with
`flock -x /home/jackmccarthy/cloud-b3/w16/lake-build.lock`, used `lean -j 1`,
and had a 40 GiB address-space bound (`ulimit -v 41943040`).

The main project library was privately reflink-copied from the parent's goldlib.
Mathlib and package libraries were read-only inputs from the reference checkout,
using an explicit `LEAN_PATH`. Outputs were written only to this lane's isolated
checkout. No parent-authored source file was modified or committed by this lane.

## Results actually obtained

Seven canonical new **definition-only prerequisites** for the independent
function-field Riemann–Roch proof compiled with exit status zero:

* `Def_ModularCurve_CanonicalDivisor`
* `Def_ModularCurve_CanonicalDivisorUniformizer`
* `Def_AlgebraicCurve_Repartitions`
* `Def_AlgebraicCurve_AdelicIndex`
* `Def_AlgebraicCurve_CanonicalDivisor`
* `Def_AlgebraicCurve_LocalResidue`
* `Def_AlgebraicCurve_RiemannRochRows`

Their remaining imports were reused from the private exact-main goldlib.
Measured maximum RSS among these seven invocations: 6,919,144 KiB.
Raw compiler/time logs are in `Preflight/`.

Two scratch preflight tests also succeeded:

1. `RR-export-symbols.log`: 375 ordinary root-export target names checked with
   `#check` using the exact RR definition imports; exit zero, no missing names.
2. `RR-header-scopes.log`: the first 344 lines (24,432 bytes) of the transformed
   first RR part, stopping before its first mathematical declaration, compiled
   with exit zero and no namespace/export/open errors.

These checks are **not compilation of any of the six proof edges**, not an
axiom report for their `solution` declarations, and not an H102 discharge.
The six proof roots and their 23 factored parts remain uncompiled pending the
parent's approved dedicated-host handover. The independent static checks of
contiguous source ranges, hashes, balanced scopes, absence of prohibited Lean
forms, and byte-identical original `solution` signatures passed separately.

## Native invocation shape

For each definition, the command was equivalent to:

```
LEAN_PATH=<private-main-lib>:<read-only-mathlib-and-package-libs> \
LEAN_NUM_THREADS=1 flock -x <shared-lock> /usr/bin/time -v \
  <Lean-4.35.0>/bin/lean -j 1 -o <private-module.olean> <canonical-source.lean>
```

Scratch availability checks used the same command without `-o`. `LEAN_PATH`
contained no changed dependency pins or new package. These are stock Lean
compiler commands; no custom checker or build-time elaborator was added.
