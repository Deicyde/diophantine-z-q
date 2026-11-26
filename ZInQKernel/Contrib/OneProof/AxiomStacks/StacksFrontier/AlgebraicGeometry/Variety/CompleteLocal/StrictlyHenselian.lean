module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Strictly henselian local rings

A local ring is strictly henselian when it is henselian and its residue field is separably
closed.

## Main definitions

* `StrictlyHenselianLocalRing` is the property of being a henselian local ring with separably
  closed residue field.

## Implementation notes

The property is a class extending both `HenselianLocalRing R` and
`IsSepClosed (IsLocalRing.ResidueField R)`. Consequently, either constituent property is
available directly by typeclass inference from strict henselianity.

## References

* [Stacks Project, Tag 03QK](https://stacks.math.columbia.edu/tag/03QK)
-/

@[expose] public section

/-- A commutative ring is strictly henselian if it is a henselian local ring and its
residue field is separably closed. -/
@[stacks 03QK]
class StrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop extends
  HenselianLocalRing R, IsSepClosed (IsLocalRing.ResidueField R)
