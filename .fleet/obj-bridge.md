# obj-bridge (fleet summary)

**Result.** `scratch/obj-bridge/Objects.lean` compiles: no errors, no sorry, no axiom; audited
declarations use only propext, Classical.choice and Quot.sound. It builds the shared object layer
for packages I2/I3. The object is I2's `Grp (Over (Spec K))` with `[IsAbelianVariety A]`, with
`K : Type`. I3's `Hom`, `End`, `End⁰`, `T_ℓ`, `V_ℓ`, `galRep`, `dim` and `tateHomZl` act on it
through `ObjBridge.ofGrp`.

- **The bridge is a bijection.** On morphisms: `homEquiv : (A ⟶ B) ≃ Hom A B`. On endomorphism
  monoids: `endMulEquiv : CategoryTheory.End A ≃* End A`. On objects: `ofGrp`/`toGrp`, both round
  trips `rfl`.
- **Points and base change agree by `rfl`.** I2's and I3's points and Galois action coincide, and
  so do their base changes (`ofGrp_baseChange`). `T_ℓ` is a functor on the shared objects.
- **All 11 I2 leaves and all 7 I3 leaves (plus `EndDivision` and `I3Leaves`) are restated over
  the shared layer.** Each comes with a compiled proof of equivalence with the original:
  - `Iff.rfl` for 9 I2 leaves and for `EndDivision`;
  - through the bridge bijection for I2-Char and I2-Rank;
  - by object round trips for the I3 leaves.
- **The I3 glue is restated and proved over the shared layer.** For example,
  `exists_hom_ne_one_of_equivariant` gives a morphism of group objects `f : A ⟶ B` with
  `f.hom.hom ≠ 1`.
- **New:** leaf I2-Rank follows from leaf I3.M1 (`homRankBound_of_homFreeFinite`). It can be
  dropped from the announced list.

**What remains.** Glue A6 (`goodReduction_of_QM_rational3`) is still `sorry` in pkg-I2 and is
omitted here. I2-Tors/I3.M0 and I2-Char/I3.M2 might also be merged, but are not; they are stated
at different levels (finite level against `T_ℓ`/`V_ℓ`). To integrate, keep §C–§F of Objects.lean
and replace the verbatim copies §A/§B with imports.

Details: `docs/research/obj-bridge.md`, `scratch/obj-bridge/log.md`.
