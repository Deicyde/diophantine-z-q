# Verified shared-core compatibility proofs

Scope: these are prerequisite checks, **not** a Mumford torsion discharge or a
verification of the complete multiplication-degree/cardinality source cone.
The final OneProof leaf and newest Main/Discharges check remain pending.

Fixed environment: Lean4.35.0 / Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.
All source declarations retain their original statements and assumptions.

## Height / quotient dimension

`P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.solution`
compiled exit0. Peak RSS7213320KiB, wall5.68s. Proof-only changes adapt the
MvPolynomial Krull-dimension formula's ENat cardinal API and make the already
available unique-factorization/GCD/integrally-closed/going-down structures explicit.
The IsGCDMonoid proposition is constructed directly; no new assumption is added.

## Depth of a regular local ring

`P2MW.S_IsRegularLocalRing_depth_self_eq_ringKrullDim.solution` compiled exit0,
including its complete copied proof prefix. The three-module stage (the unchanged
verified CompatFlatness quotient helper, Patching_SystemTypes, and this source
module) had peak RSS7418276KiB, wall20.68s. Proof-only fixes qualify Module.depth,
make the existing quotient-module finiteness explicit at two basis calls, and
replace a private root-self-export with the module-local private helper. The
public solution's type is unchanged.

## Actual axiom check

The one lane scratch imported the two source modules and NativeBridges:

```
lake env lean -M16000 Check.lean
```

Exit0, peak RSS7166828KiB, wall4.85s. Exact output:

```
'P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'P2MW.S_IsRegularLocalRing_depth_self_eq_ringKrullDim.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.finite_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Regular-stalk carrier

The original `Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks` module
compiled exit0 after adding the explicit Field type to `hf.toField` for the
localization of a dual-number ring. Its source guard-message axiom tests all pass.
Peak RSS6886672KiB, wall6.48s. The proof and all statement assumptions are retained.
