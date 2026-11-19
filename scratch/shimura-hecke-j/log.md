# Results log

- VERIFIED (source): `HeckePin.end_eq_of_classes` reduces pinning to a
  pointed constancy test. `HeckePin.X1TauPoints` states existence of
  realizations; it has no proof in the tree. `WeberField.lean` supplies
  holomorphic coordinates, without the required stalk and residue comparison.
- VERIFIED (Lean): `tauGammaOne` proves the full `AtTau` predicate invariant
  under a lift of the unit class `1`.
- VERIFIED (Lean): `constOnTauPoints_of_realization : X1TauPoints →
  ConstOnTauPoints` via one test over a closed point and one over the generic
  point. `isXi_unique` pins endomorphisms given `X1TauPoints`.
- VERIFIED (Lean): `isXi_prime_of_isHeckeT` proves the exact prime action.
  `isXi_bad_prime_pow` proves the bad-prime power action given realization
  and single valuedness of `AtTau`. `isUpper_mul` composes upper branches
  at any positive indices by reindexing the offsets.
- VERIFIED (Lean): `exists_xi_of_compositeActions` gives the exact per-model
  `XiAction` and `HeckeRelations` from the existing prime formulas, point
  realization and single valuedness, and the two remaining closure laws.
- OPEN: unique realization of `AtTau`; coprime and good-prime product
  identities for the specified representatives on `Γ₁(N)` orbit divisors.
  The `Γ₀(N)` composite table and modular-form equalities do not supply
  those orbit identities, with their diamond twist, in the tree.
- VERIFIED (build): `lake build +ZInQKernel.Contrib.OneProof.ShimuraHeckeJ`;
  the two new prerequisite modules and the main new module built. The
  detection module emits the Mathlib import module-system advisory.
  The existing `SameDimFinite` also built.
- VERIFIED (axioms): 26 theorem outputs in `Axioms-output.txt`; only
  `propext`, `Classical.choice` and `Quot.sound`.
- VERIFIED (focused): `lake env lean scratch/shimura-hecke-j/DischargesFocused.lean`.
  The conditional composite elaborates at the exact quotient-row type.
  `Discharges-output.txt` retains the printed statement and the Hecke bridge
  for `ShimuraSteps.shimuraThm1Af_of_printed'`.
- NOT APPLICABLE: print-only composite and combined dry run. No fold and no leaf.
