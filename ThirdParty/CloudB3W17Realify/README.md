# W17 realification — partial foundations

Import `ZInQKernel.Contrib.CloudB3W17Realify.Realification`.

## Results

All statements are universe-polymorphic and hold for every `n : ℕ∞ω`, including
analytic `ω`. Existing topology, `ChartedSpace`, and group operations are retained.
The real and complex scalar actions must be compatible (`IsScalarTower ℝ ℂ E`).

- `CloudB3W17Realify.isManifold_real`: `IsManifold 𝓘(ℂ,E) n M` implies
  `IsManifold 𝓘(ℝ,E) n M`.
- `CloudB3W17Realify.contMDiff_real`: complex `ContMDiff` implies real `ContMDiff`.
- `CloudB3W17Realify.lieGroup_real` / `lieAddGroup_real`: complex Lie (additive)
  group structure implies the corresponding real structure.
- `ScalarRestriction.lean` also proves general normed-subfield versions,
  `contMDiffWithinAt`/`At`/`On`, and `ContMDiffAdd`/`Mul` restriction. General
  models must have equal underlying `PartialEquiv`s. This condition directly
  covers product self-models, so multiplication is not smuggled through a
  different charted-space structure.

These theorems **do not construct an exponential map or prove uniformization or
GAGA**. They remove the scalar-field obstruction to applying the real manifold
ODE API on a complex analytic Lie group. No OneProof field closure is claimed.

## Source basis and proof

Base `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`;
Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Mathlib's `ContDiffWithinAt.restrict_scalars` explicitly supports `ω`.
For the manifold assertion apply `isManifold_of_contDiffOn` to the unchanged
atlas and restrict scalar fields on transition maps. For maps use
`contMDiffWithinAt_iff`: extended charts are equal, continuity is unchanged,
and the ordinary `ContDiffWithinAt` term restricts scalars. Lie structures
follow from these map results and the transferred manifold structure.

Note that Mathlib's `LieGroup` does inherit `IsManifold` transitively through
`ContMDiffMul` (`Geometry/Manifold/Algebra/Monoid.lean`).

## Verification

Both new modules were compiled to olean/ilean artifacts by sequential direct
Lean invocations, one Lean process at a time:

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify
lake env lean -M6144 -j4 \
  -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/ScalarRestriction.olean \
  -i .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/ScalarRestriction.ilean \
  ZInQKernel/Contrib/CloudB3W17Realify/ScalarRestriction.lean
lake env lean -M6144 -j4 \
  -o .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/Realification.olean \
  -i .lake/build/lib/lean/ZInQKernel/Contrib/CloudB3W17Realify/Realification.ilean \
  ZInQKernel/Contrib/CloudB3W17Realify/Realification.lean
```

Both exit 0 without warnings. Maximum peak RSS: 2,911,556 KB (under 3 GB).
The scratch import/usage check proves generic `ω`, lowered `∞`/`1`, finite `3`,
and concrete `Fin 2 → ℂ` usage. Its `#print axioms` on **all 16 declarations**
reports exactly `[propext, Classical.choice, Quot.sound]`.
Scratch evidence is in the W17 scout working directory:
`RealifyCheck.lean` and `Realify-Axiom-Output.txt`.

No full repository build was run. No OneProof.Main import, `sorry`, new axiom,
`#eval`, `run_cmd`, initialization, new syntax/notation, macro, elaborator, or
`native_decide` occurs in either delivered Lean module. Only new files were
added. No public push or GitHub write was made.
