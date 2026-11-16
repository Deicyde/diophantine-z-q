# W13 D5 author handoff — bounded, partial kernel verification

Date: 2026-11-16.
Branch: `cloud-b3/w13-d5`.
Author lane: subagent 3, zero children spawned.
Working base: `2dc949d688c407e32823c4e751679d66b2f40e65` (restored main; H119/interface types unchanged).

## Grade

**The complete D5 converse is NOT yet kernel-verified. No H119 or discharge pass is claimed.**

Four main-only support modules, `Construction`, and three verification modules have been compiled successfully from source. `Construction` retains main's original `SGRSplit.abVarSurfaceRelDim` and uses the normalized core's canonical existing main Galois providers. `Generation`, `Assembly`, `Count`, and `Checks/Assembly` remain unbuilt pending the normalized geometric torsion-cardinality cone. The parent requested bounded remaining spend after the newer route-NV fold made H119 a fallback; no missing 1378-module cone or full world was cold-built in this lane.

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
- `Construction` (compiled): FakeEC at N=1 with original carrier/action/law; actual identity subgroup; canonical tangent trace provider plus main's unchanged `SGRSplit.abVarSurfaceRelDim`. The actual arbitrary-geometric-field `kernelAct_trace` and all N=1 FakeEC fields compile with only standard axioms.
- `Generation` (unbuilt): actual `eta(1)` as distinguished point; genuine arbitrary-geometric-field torsion cardinality 81 supplies generation, and the original kernel supplies the annihilator.
- `Transport`: explicit Eq.rec transport of surface/action/level, with carrier-aware hom/point formulas and a kernel object isomorphism. `Checks/Transport` now verifies the dependent packaging shape with `Over.mk P.A.X.hom` behind the genuine `hiddenCarrier` definition, matching Assembly rather than using a literal `P.A.X` carrier.
- `Assembly` (unbuilt): uses the verified transport helpers, not goal-wide `rw [hA]`. The two carrier equations now compose the helper equality with `.trans` and close the identity composition using `erw`, which unfolds the hidden `Over.mk` carrier enough for `eqToHom_refl`.

## Hidden-carrier follow-up, 2026-11-16

Independent review found that the first fixed-carrier check at `ffa6b8495175f875c56f8adddabcf62dff8a1631` was not faithful: it used `X := P.A.X` literally, whereas Assembly uses `Over.mk P.A.X.hom` behind a definition. The two `simpa only [eqToHom_refl, ...]` steps therefore still failed in the reviewer's faithful reproduction.

The source fix is the tested `.trans` / `erw` pattern for both action and level equations. The strengthened `Checks/Transport.lean` uses the hidden carrier and copies these exact clause proofs. It was rebuilt from source successfully in **6.13s**, peak RSS **6,876,424KiB**, with exactly `[propext, Classical.choice, Quot.sound]`. `Checks/Foundations.lean` was rerun successfully in **5.53s**, peak RSS **8,795,068KiB**, and every printed support/regression conclusion again has exactly those standard axioms.

This verifies the bounded carrier-unfolding repair in the faithful reproduction, **not** the complete Assembly or D5 dependency graph. Full D5/H119 remain unbuilt/unverified.

## Canonical-provider Construction check, 2026-11-16

The normalized 75-module core initially collided with the existing main SGR closure because three new TateCp copies redeclared the same root names as main's canonical CloudB2X0Transitive providers. The normalizer fixed this in `52136f73128cf9abc692b8bf6bcbcd63b927a2c9`, retargeting the new imports to the identical canonical existing providers and removing only the three new duplicates. The remaining 72-module core was compiled by that lane; its exact ignored warm cache was copied into this lane, and the obsolete three cache files were dropped. No provider source was changed in the D5 lane.

The original `ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard` import and `SGRSplit.abVarSurfaceRelDim` supplier are retained. An attempted narrow dimension helper was not integrated or banked. Two minor structure-field binder errors (`lev_stable` and `lev_fibre`) were fixed by explicit binder introductions, without statement or mathematical-data changes.

Actual bounded tests on Lean 4.35.0 / mathlib 56a005, one `lean -j2 -M11264` process at a time:

- `Construction`: **pass**, 27.54s, peak RSS **8,714,268KiB**.
- `Checks.Construction`: **pass**, 4.96s, peak RSS **8,737,144KiB**.
- The actual `kernelAct_trace`, `identityLevelEquiv`, `kernelFakeEC`, and `kernelFakeEC_act` all print exactly **`[propext, Classical.choice, Quot.sound]`**. The typed FakeEC example also compiles.

This proves the actual tangent bridge and the complete original-carrier N=1 FakeEC construction. It does **not** prove full-level-three generation or the complete D5 converse. No Generation or 1378-module torsion cone was built.

## Still required

1. Import-ready normalized geometric torsion-cardinality cone, with warm compiled dependencies. The trace/interface core is now ready and used by Construction.
2. Build `Generation`, `Assembly`, `Count`, and `Checks/Assembly` against those exact definitions; repair any real errors.
3. Check `d5_obligation`'s exact type and full axioms. Any H119 integration/discharge is the lead's separate verification, not supplied by this partial handoff.

## Scope and provenance

All task source additions are under `ZInQKernel/Contrib/CloudB3W13/Dictionary/D5/`; no existing repository module or pin was edited. No OneProof.Main production import, new PortUtilExt, prohibited proof placeholder, native_decide, build-time evaluator, syntax, notation, macro, or elaborator was added. No PR, issue edit, main push, human outreach, non-D5 port repair, or child spawn was performed.

Canonical FLT inputs are from Anthropic's Apache-2.0 development at `6e837e75355538c7f80bab5b956861e86c4eacc2`, reused through the existing/public or lead-retargeted providers. Their licences/credits are retained; the new files identify their own original W13 D5/Metamate assistance. The seven old D5 bodies were lost and were not represented as recovered.
