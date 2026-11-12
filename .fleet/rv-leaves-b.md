# rv-leaves-b (fleet report)

**Verdict.** I reviewed 35 leaves: 11 in pkg-I2, 7 in pkg-I3, 15 in pkg-I6 (counting the cochain
forms) and 2 in glue-conductor. None is WRONG, STRONGER THAN PUBLISHED or VACUOUS. All are
faithful Lean statements. Some need citation repairs before the announcement:
- **I3.Q `QMDichotomy`** combines Mumford §19, §21 and Silverman III.9.4; there is no single
  locator. My own claim that definite B needs Shimura was wrong and is retracted.
- **I3.M3 `PoincareReducibility`** should cite Milne 1986 Prop. 12.1, because Mumford works over
  k̄.
- **I6.2a–c** use Mathlib's `continuousCohomology`. Its comparison with inhomogeneous cochains is
  a TODO in Mathlib, so I recommend announcing the cochain forms I6.2a′–c′.
- **glue-conductor's global different leaves** need a citation for the localization of the
  different and of `G_i`; or use I6.6/I6.7 instead.

**Object layer.** It matches the standard objects:
- I2's and I3's abelian varieties are identical: proper, smooth, geometrically integral group
  objects in `Over (Spec K)`.
- The Galois action on points is a left action with the correct (contravariant) composition.
- `T_ℓ` is the limit of `A[ℓⁿ](K̄)` under multiplication by ℓ.
- Inertia is Mathlib's stabilizer and residue-kernel (checked in Mathlib).
- The lower groups, `φ`, the upper numbering and the Artin conductor follow Serre, *Corps
  locaux*.
- `ZMod 2` carries the discrete topology (checked), so the continuity conditions are real.

Two gaps:
- `ρ_ℓ` is not defined as continuous. Continuity is provable glue, needed only for C10.
- No nonzero abelian variety can be built in Mathlib, so faithfulness of the I1/I4 objects carries
  the weight.

**Shared layer.** Use I2's `Grp (Over (Spec K))` with `[IsAbelianVariety]` as the object, and take
I3's `Hom`/`End`/`End0`/`T`/`V`/`galRep` through the bridge `RvLeavesB.ofGrp`/`homOfGrp`. Fix one
universe.

**Compiles.** `scratch/rv-leaves-b/Repairs.lean` passes `lake env lean` with no errors, warnings or
sorry. It contains I3's definitions, the I2→I3 bridge (the `Hom` map is shown to be the identity on
underlying morphisms by `rfl`) and an optional narrower `QMDichotomyIndef` (`0 < a`).

**Remains.** Locators are UNVERIFIED (no network). Glue still carrying `sorry`:
- A6 `goodReduction_of_QM_rational3`;
- D4 `artinConductor_le_of_upper`;
- D3 in I6 (already proved in glue-conductor/Dyadic.lean);
- continuity of ρ_ℓ.

The bridge is a map on Hom sets; I did not prove it is a bijection.

Report: docs/research/rv-leaves-b.md.
