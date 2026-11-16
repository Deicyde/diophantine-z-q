# Retained math/API compatibility: all 22 compiled roots

This is a staged H102 source-port checkpoint, not final degree/cardinality or
Mumford discharge evidence. The first provider DAG and its 124 failures are a
historical first pass; no final impossibility or missing-degree assumption is inferred.

At Lean4.35/Mathlib56a00585, these nine primary-retained modules now compile:

- All seven definition modules from `compat-ownership-proposed.json.primary_retained`:
  SymmetricPower, LocalRepresentabilityULift, ProjTwistDatum, ExteriorPower,
  PullbackMonoidal, InternalHom, CurveModelSmooth.
- Source proofs S_Module_depth_quotSMulTop_succ_eq and
  S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.

Changes retain the same mathematical objects and hypotheses. The Aut one-field
representation is addressed via Aut.of and asIso; the presheaf-of-commutative-ring
abbreviation is definitionally the original forgotten-ring presheaf; the source
maps and tensor structures are not replaced. Residual source-local shorthand is
expanded literally rather than introducing new notation. Scalar-tower/ring/module
instances and existing proof constants are supplied explicitly where inference
became ambiguous. Copied depth-prefix fixes are those independently compiled in
the existing shared core, not new mathematical assumptions.

Actual scratch command `lake env lean -M16000 Check.lean` returned0,4.86s,
7175412KiB peak RSS. Exact kernel outputs:

```
'AlgebraicGeometry.finFibrePow.permAut' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicGeometry.Scheme.LocalRepresentabilityULift.comp_toGlued_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AlgebraicGeometry.ProjSpace.frameUnit_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PresheafOfModules.exteriorPowerMap_app_ιMulti' depends on axioms: [propext, Classical.choice, Quot.sound]
'PresheafOfModules.restrictScalars_laxMonoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
'PresheafOfModules.tensorIhomAdj' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicCurve.CurveModel.rank_kaehler_chartRing_localization_away_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'P2MW.S_Module_depth_quotSMulTop_succ_eq.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Complete retained-22 checkpoint

All 22 primary-retained modules now compile on the pinned toolchain. The fresh
`CheckRetained22.lean` imports exactly those 22 modules and prints axioms of the
seven definition APIs plus all 15 original `solution` declarations. Exit0,
4.79s,7205712KiB peak RSS: all **22 actual axiom lists** are exactly
`[propext, Classical.choice, Quot.sound]`.

Additional repairs preserve the original telescopes: absolute namespace exports/
opens, discarding absent registration aliases, one-based TFAE list positions,
new tensor induction forms, explicit free vector-space and scalar-tower proofs,
and the current AddMonoidAlgebra coefficient representation. Restoring the current
`backward.isDefEq.respectTransparency=true` setting removes speculative scalar
instance loops; the remaining definitional coercions are addressed by local
`change`, `rfl`, or `erw`, not assumptions. A module-private zero-coefficient lemma
is reflexivity only. The original geometric retraction and invertible-ideal
arguments remain the source proofs, not substituted providers.

A33/B33/C32 compatibility ownership is disjoint; the primary does not edit those
98 modules after transfer, nor the separately assigned finite3,
flat22, RR55 or giant6. Foreign verified source/cache is consumed unchanged with
payload/source SHA checks. The final original torsion theorem has no additional
provider hypothesis, but is not claimed as proved until its actual degree/cardinality
root and newest Main/Discharges/axiom checks succeed.
