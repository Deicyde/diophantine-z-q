# Exact original-law geometric bridges: verified

Scope: the complete native/relative prerequisite bridge is verified. This is **not**
the final Mumford torsion discharge: the full multiplication-degree/cardinality
provider and newest Main/Discharges scratch still require validation.

All 25 pinned FLT geometry prerequisites compiled at the unchanged Lean4.35.0 /
Mathlib56a00585 pins. RelativeBridges.lean then compiled exit0 (70.74s,
13089888KiB peak RSS) on the dedicated node.

## Important law-preservation point

The bridge does not replace the group structure on `A.X` by a new structure on
`Over.mk A.X.hom`. Instead, `pointOverEquiv` identifies the genuine scheme-map
structure equation with morphisms **into the original `A.X`**. `relativeLaw`
transports the original `A.grp` multiplication, identity and inverse through that
equivalence, including naturality. The `Spec k/k` comparison only precomposes by
an identity-on-underlying-schemes over-category isomorphism.

Consequently, `pointEquiv_mul`, `pointEquiv_pow` and `torsionEquivRelative` refer
to the original multiplicative law and original torsion set in TailQ1257. The
Krull-dimension input is the exact original topological dimension, transferred
through the homeomorphism from the whole-space subtype, with no characteristic-zero,
positive-dimension or additional geometric hypothesis.

## Actual kernel axiom evidence

```
lake env lean -M16000 Check.lean
```

Exit0,4.85s,7172120KiB peak RSS. The one scratch imported RelativeBridges and the
independently verified generic finite-group helper. Exact output:

```
'ZInQ.Contrib.CloudB3W16Torsion.relativeLaw_commutative' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.abelianSchemePropertyBundle' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.smoothOfRelativeDimension' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.pointEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.pointEquiv_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.torsionEquivRelative' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16FiniteGroup.nonempty_torsionBy_addEquiv_pi_zmod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The final leaf draft has the exact type `AvSplit.MumfordTorsionAlgClosed` and no
additional argument, but is intentionally not described as closed until its complete
imported degree provider compiles and the independent exact-discharge check succeeds.
