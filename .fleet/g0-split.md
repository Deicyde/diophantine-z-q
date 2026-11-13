# g0-split (2026-11-12): the H-decomposition `sorry` split into named pieces

**Result.** `HSyn.glueOutputs_of_leaves` (the only `sorry` of `scratch/h-decomposition/Leaves.lean`)
is now proved in `scratch/g0-split/Split.lean`. Its hypotheses are `ResearchLeaves`,
`TextbookLeaves`, two concrete leaves (leaf-push2's R18 and R22, transported here because
`r.r18` and `r.r22` are still placeholders) and ten named glue pieces. Each piece is a
`def … : Prop` whose docstring names its glue step. VERIFIED: `lake env lean
scratch/g0-split/Split.lean` gives 0 errors and no `sorry`. `#print axioms` is
`[propext, Classical.choice, Quot.sound]` for `glueOutputs_of_leaves`, `sixContactMin_of_leaves`
and the new proved pieces.

**The missing pieces, smallest first** (sizes SPECULATIVE):
1. `DimFinite`
2. `DimBaseChange`
3. `X1BelyiOnModel` (BelyiX1 on the IsJ1 model)
4. `FibreSimple` (G5-G6 on A)
5. `HeightAdditivity` (E4)
6. `StableHeightBaseChange`
7. `ProductExists` (G17)
8. `ReverseIsogeny` (G17)
9. `ThetaPointOfFibre` (G19, F1 on A)
10. `ModularConstituent` (G2, G4, G7-G16: field `L'` and model `A/L'`, `[L':ℚ] ≤ QM`,
    `N ≤ QM²`, `J₁(N)`, and a common constituent of the Tate modules). This one is the bulk.

**Proved and applied (new or existing):**
- A4 (`exists_fibre_object`)
- `model_dim`
- H5 finiteness
- E1 (with glue-ssbc's `SemisimpleBaseChange` copied in)
- T8 (Poincaré)
- `dim_J1_le` (T34)
- `javanpeykarJ1` (from R18 + piece 3)
- `thetaPazuki` (from R22 + piece 9, at the hardened `x + 3`)
- `isogenousProduct` (from pieces 1, 7, 8)
- `transfer_core`: all E3-E4 numerics of `NonCMOutput` from R19, R20 and R21, including `log κ`
  computed.

The CM disjunct is not used (NoCM).

**Soundness note.** A first draft quantified the modular piece over every number-field model of
the fibre. That piece is false (models over fields of degree > QM), so the reduction would have
been vacuous, and it compiled anyway. Now the piece produces the field and the model together.
Truth of the pieces: model reasoning only (doc §3). It inherits def-faltings' correctness (H5)
and the premise bp-qmmoduli §2.2.

**Remains:** the ten pieces. Integration recipe: doc §4. Report: `docs/research/g0-split.md`.
Log: `scratch/g0-split/log.md`.
