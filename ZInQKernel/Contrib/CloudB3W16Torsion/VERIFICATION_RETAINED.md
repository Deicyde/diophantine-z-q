# Retained math/API compatibility: nine compiled roots

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

The remaining 13 retained roots are tested and repaired against their current
code separately. A33/B33/C32 compatibility ownership is disjoint; the primary does
not edit those 98 modules after transfer, nor the separately assigned finite3,
flat22, RR55 or giant6. Foreign verified source/cache is consumed unchanged with
payload/source SHA checks. The final original torsion theorem has no additional
provider hypothesis, but is not claimed as proved until its actual degree/cardinality
root and newest Main/Discharges/axiom checks succeed.
