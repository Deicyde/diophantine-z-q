# Build and proof checks

Verified proof head: `97df90e7d2412d45f44c2ca2143579fe4ad8b5b7`.
Rebased on fetched main `e22df37cdef936f5b0f29ec09501854bea6c7316`.
Host: a dedicated internal build host; own author checkout.
Lean `4.35.0`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Results

The full named build of all seven supplier modules succeeded: **3920 jobs, exit 0**.
It rebuilt `ChowSurjective`, `PointLift`, `ProjBridge`, `ProjectiveChowCover`,
`NativePresentation`, `NativeCompact`, and `AbVarCompact`.

The subsequent `FinalCheck.lean` run succeeded: **exit 0**. Its full output is
`CHECK_OUTPUT.txt`. It checks all thirteen supplier constants and reports the
axioms of those constants and both projective-compactness donors. All fifteen
reports are exactly `[propext, Classical.choice, Quot.sound]`.

The check command was:

```
lake env lean -j4 scratch/CloudB3W17ProperCompact/FinalCheck.lean
```

The full build output remains in the checkout at
`scratch/CloudB3W17ProperCompact/FinalBuild.out`. Warnings are module-system and
old-API lints; the build reports no errors.

## Source checks

- Comment/string-aware prohibited-code/import scan: **52 new Lean files clear**,
  including seven own supplier modules and 45 Lean files in the two committed
  Hodge slices. No `sorry`, extra axiom, `native_decide`, new parser/notation,
  macro/elaborator, initializer, `#eval`, or `OneProof.Main` import.
- All supplier/dependency Lean files are below 150 KB.
- Both immutable Hodge snapshots match byte for byte: core
  `e222d7ba1999d47ab0618cc0d812bb0b6f8b7229` (29 files) and companion
  `9fbc627ae28ffa756cdf33f2c8995eddce06601a` (20 added files). No producer checkout
  or Hodge source was edited.
- Target H103/H105 declarations, `Objects.lean`, toolchain and Mathlib manifest
  are unchanged from the fetched main.
- Own branch has no upstream and `push.default=nothing`. No public GitHub write
  or human outreach was performed.

## Scope

This proves native compactness for integral proper complex schemes and every
actual `PkgI3.AbVar ℂ`. No target projectivity or `CompactSpace` assumption is
used. It does not cover arbitrary nonreduced proper schemes or discharge H103:
the native-to-project point/evaluation/topology dictionary is a separate supplier.
No `#discharges` closure result is claimed for these partial modules.
