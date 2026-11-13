# igusa-generic results log

## 2026-11-13
- Split agreed with igusa-special (cross-session message): split on `det (Matrix.of (PkgI1.yv f))`.
  Their side: `SeparationBothSpecial` (both det yv f = 0 and det yv g = 0).
- `ZInQKernel/Contrib/T28/Generic.lean`: `T28.GenericLocus`, `T28.SeparationGeneric`,
  `T28.SeparationSpecialLocus`, `T28.SeparationBothSpecial`, `T28.sexticAct_symm`,
  `T28.igusaSeparationEq_of_split`, `T28.igusaSeparationEq_of_generic_bothSpecial`,
  `T28.igusaClebschSeparation_of_split`, `..._of_generic_bothSpecial`. VERIFIED: compiles
  (`lake env lean`, no errors).
