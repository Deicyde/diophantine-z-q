# Selected prerequisite axiom excerpts

These are selected, verbatim excerpts from historical successful prerequisite
checks. This file is **not** a full raw compiler transcript, an exhaustive API
listing, or evidence that the degree/cardinality provider or Mumford leaf passed.
The unchanged original transcripts are preserved privately.

## Retained API checks

```text
'AlgebraicGeometry.finFibrePow.permAut' depends on axioms: [propext, Classical.choice, Quot.sound]
'PresheafOfModules.exteriorPowerMap_app_ιMulti' depends on axioms: [propext, Classical.choice, Quot.sound]
'PresheafOfModules.tensorIhomAdj' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Later primary source checks

```text
'AlgebraicCurve.CurveModel.nonempty_body' depends on axioms: [propext, Classical.choice, Quot.sound]
'P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Compatibility-lane API sample

```text
AlgebraicCurve.Place.exists_forall_ord_eq_finset.{u_1, u_2} {K : Type u_1} {F : Type u_2} [Field K] [Field F]
  [Algebra K F] (S : Finset (AlgebraicCurve.Place K F)) (n : AlgebraicCurve.Place K F → ℤ) :
  ∃ g, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v
'AlgebraicCurve.Place.exists_forall_ord_eq_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three source families still require their stated reproduction checks; these
selections do not replace a check of the exact final publication head.
