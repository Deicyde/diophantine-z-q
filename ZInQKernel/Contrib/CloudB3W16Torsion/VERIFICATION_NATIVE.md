# Native torsion bridge verification

This is **not** an H102 discharge or verification of the degree/cardinality provider.
The full exact leaf remains unvalidated until its complete geometric provider and
Main/Discharges acceptance scratch compile.

## Verified native proofs

At the unchanged Lean4.35.0 / Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679
pins, NativeBridges.lean compiled with exit0. Its imports are the existing original
object definitions and the closed H101 arbitrary-base multiplication proof. The
field is arbitrary, and no characteristic-zero or positive-dimension condition
is introduced.

- Original `PkgI2.torsion` is equivalent to the additive torsion subgroup of the
  original point group, respecting original multiplication.
- Multiplication by a natural number nonzero in the field is étale.
- That multiplication is finite by properness plus local quasi-finiteness.
- The original torsion set over an algebraically closed field is finite, via
  injection into the set-theoretic fibre of the multiplication map over the unit.

Finiteness is **not** substituted for the missing numerical cardinality equality.

## Actual axiom scratch output

Command on the shared host, under the team flock and LEAN_NUM_THREADS=4:

```
lake env lean -M4096 Check.lean
```

Exit0; peak RSS3916412KiB; wall3.01s. Check.lean imported NativeBridges and the
independently verified finite-group helper and contained only the five axiom prints.

```
'ZInQ.Contrib.CloudB3W16Torsion.torsionEquivAddSubgroup_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.multiplication_etale' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.multiplication_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16Torsion.finite_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.CloudB3W16FiniteGroup.nonempty_torsionBy_addEquiv_pi_zmod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Distinct provider-stage outcomes

The first source-carrier attempt with an umbrella Mathlib import and -M4096
stopped before meaningful mathematical diagnostics on a Lean interpreter memory
exception, stagepeak6321352KiB. On the shared host, a temporary narrow import list
compiled the carrier and RelativeGroupLaw definitions; the next GrpObj bridge
reported missing standard imports, not a mathematical hypothesis. The dedicated
host uses the original carrier import and adequate memory, and explicit standard
Grp/Over/Abelian imports are now present. Neither failed stage is closure evidence.
