# W13 D5 author handoff — bounded, partial kernel verification

Date: 2026-11-16.
Branch: `cloud-b3/w13-d5`.
Author lane: subagent 3, zero children spawned.
Working base: `2dc949d688c407e32823c4e751679d66b2f40e65` (restored main; H119/interface types unchanged).

## Grade

**The complete D5 converse is NOT yet kernel-verified. No H119 or discharge pass is claimed.**

Four main-only support modules and two verification modules were rebuilt successfully from source after the final print-hygiene edits. `Construction`, `Generation`, `Assembly`, `Count`, and `Checks/Assembly` remain unbuilt pending normalized recovered dependency cones. The parent requested bounded remaining spend after the newer route-NV fold made H119 a fallback; no missing 1378-module cone or full world was cold-built in this lane.

## Exact intended export

Module: `ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Assembly`.
Compatibility import: `ZInQKernel.Contrib.CloudB3W13.Dictionary.D5.Count` (imports Assembly; declares nothing).

```lean
ZInQ.Contrib.CloudB2Shimura.Dictionary.D5.d5_obligation :
  ZInQ.Contrib.CloudB2Shimura.Dictionary.D5_Obligation
```

The source theorem has no final premises. Its **source exists, but this declaration's actual compilation and axioms have not been checked**.

## Actual verified source builds

Pinned environment: Lean 4.35.0 / mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Initial bounded verification run (before the hidden-carrier follow-up): `-j2 -M11264`, `LEAN_NUM_THREADS=2`, one Lean process at a time, `/usr/bin/time -v`, warm root `.lake` and warm local helper-package `lean/.lake`.

| module under `CloudB3W13.Dictionary.D5` | wall seconds | peak RSS (KiB) | result |
| --- | ---: | ---: | --- |
| `FiniteLevel` | 4.43 | 6,919,984 | pass |
| `KernelGroup` | 4.85 | 7,184,584 | pass |
| `GeometricPoints` | 5.65 | 8,824,584 | pass |
| `Transport` | 4.11 | 6,916,920 | pass |
| `Checks.Transport` | 4.24 | 6,916,640 | pass |
| `Checks.Foundations` | 5.10 | 8,807,032 | pass |

`Checks/Foundations.lean` prints the axioms of all listed support conclusions and of the fixed-carrier regression: **exactly `[propext, Classical.choice, Quot.sound]`**. Production files contain no axiom-print commands; they are confined to the unimported verification files.

## Source mathematics retained

- `KernelGroup`: canonical relative group law of the original kernel `A.grp`, genuine proper/smooth/connected bundle, original carrier dimension, actual rational sections, and the identity subgroup. Point multiplication is proved with named `Hom.mul_def` / `Over.lift_left` projection lemmas, point-object normalization, and congruence, avoiding expensive kernel delta-equality of Over instance data.
- `FiniteLevel`: the original 81 `liftO` representatives are distinct from the exact original kernel `3O`; equal cardinality of genuine torsion then proves generation without replacing the given points.
- `GeometricPoints`: original eta is precomposed with the actual field-spectrum map. `Epi` of field spectra proves its kernel remains exactly `3O` at every field map.
- `Construction` (unbuilt): FakeEC at N=1 with original carrier/action/law; actual identity subgroup; canonical tangent trace provider plus main's `SGRSplit.abVarSurfaceRelDim`.
- `Generation` (unbuilt): actual `eta(1)` as distinguished point; genuine arbitrary-geometric-field torsion cardinality 81 supplies generation, and the original kernel supplies the annihilator.
- `Transport`: explicit Eq.rec transport of surface/action/level, with carrier-aware hom/point formulas and a kernel object isomorphism. `Checks/Transport` now verifies the dependent packaging shape with `Over.mk P.A.X.hom` behind the genuine `hiddenCarrier` definition, matching Assembly rather than using a literal `P.A.X` carrier.
- `Assembly` (unbuilt): uses the verified transport helpers, not goal-wide `rw [hA]`. The two carrier equations now compose the helper equality with `.trans` and close the identity composition using `erw`, which unfolds the hidden `Over.mk` carrier enough for `eqToHom_refl`.

## Hidden-carrier follow-up, 2026-11-16

Independent review found that the first fixed-carrier check at `ffa6b8495175f875c56f8adddabcf62dff8a1631` was not faithful: it used `X := P.A.X` literally, whereas Assembly uses `Over.mk P.A.X.hom` behind a definition. The two `simpa only [eqToHom_refl, ...]` steps therefore still failed in the reviewer's faithful reproduction.

The source fix is the tested `.trans` / `erw` pattern for both action and level equations. The strengthened `Checks/Transport.lean` uses the hidden carrier and copies these exact clause proofs. It was rebuilt from source successfully in **6.13s**, peak RSS **6,876,424KiB**, with exactly `[propext, Classical.choice, Quot.sound]`. `Checks/Foundations.lean` was rerun successfully in **5.53s**, peak RSS **8,795,068KiB**, and every printed support/regression conclusion again has exactly those standard axioms.

This verifies the bounded carrier-unfolding repair in the faithful reproduction, **not** the complete Assembly or D5 dependency graph. Full D5/H119 remain unbuilt/unverified.

## Still required

1. Import-ready normalized trace/interface and geometric torsion-cardinality cones, with warm compiled dependencies.
2. Build `Construction`, `Generation`, `Assembly`, `Count`, and `Checks/Assembly` against those exact definitions; repair any real errors.
3. Check `d5_obligation`'s exact type and full axioms. Any H119 integration/discharge is the lead's separate verification, not supplied by this partial handoff.

## Scope and provenance

All task source additions are under `ZInQKernel/Contrib/CloudB3W13/Dictionary/D5/`; no existing repository module or pin was edited. No OneProof.Main production import, new PortUtilExt, prohibited proof placeholder, native_decide, build-time evaluator, syntax, notation, macro, or elaborator was added. No PR, issue edit, main push, human outreach, non-D5 port repair, or child spawn was performed.

Canonical FLT inputs are from Anthropic's Apache-2.0 development at `6e837e75355538c7f80bab5b956861e86c4eacc2`, reused through the existing/public or lead-retargeted providers. Their licences/credits are retained; the new files identify their own original W13 D5/Metamate assistance. The seven old D5 bodies were lost and were not represented as recovered.
