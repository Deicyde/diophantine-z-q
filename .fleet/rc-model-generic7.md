# rc-model-generic7 (fleet note)

- **Retired: none yet.** No frozen field retired, no hypothesis of `oddStagedOfSamePlace` discharged.
- **No error verdict.** No leaf added or proposed.
- **Main result / scoped stop.** Complete:
  - item 1 (doc fixes);
  - item 2 for formula-carrying (R0) seams over every algebraically closed `K` of characteristic 0 with `#K = 𝔠` (`rationalPoints_atkinRat_formulaSeam`, by transport along `K ≃+* ℂ`, with no function-field step);
  - item 3 foundations: (a), (b), (c), the naturality of `Y0LevelPoints`, the cyclicity of `C_Q`, R0 (`FormulaSeam`, `exists_formulaSeam`), R1′ (`oddVelu_reduceHom`) and R2 (`veluPointMap2_reduceHom`, `veluQuotient2_map_*`).

  Scoped stop for R3 (the composite reduces; medium) and for the every-seam form of item 2 (needs T3; generic8 does not use it).
- **Pieces supplied.**
  - `point_W`: `PointW`, `atkinLevelAlg` and `Wint_left` (under `ModelGeneric5.levelCommRing`), in `RC/ModelGeneric7/Interface.lean`, placed exactly as the INTERFACE block. The special-fibre action is generic8's.
  - `point_frob`: `Y0LevelPoints_algEquiv` / `Y0LevelPoints_comp` (`RC/ModelGeneric7/Y0Points.lean`), an input of point_frob's `Y0LevelPoints` half (SP2).
- **What compiles.** 8 modules under `ZInQKernel/Contrib/OneProof/RC/ModelGeneric7/`, each `lake build` clean, axioms `propext`, `Classical.choice`, `Quot.sound`.
- **What remains.**
  - R3, which may be bypassed by generic8's R4 through `FormulaSeam` with R1′/R2;
  - item 2 for every seam (T3, or uniqueness of separable quotients, Silverman III.4.11–4.12, UNVERIFIED);
  - `atkinLevel_moduli_special` (generic8).

  The report is `docs/research/rc-model-generic7.md`, with "What generic8 needs" and Lean names and file:line.
- **Copies.** `equivalent` of `Y0LevelPoints` (verbatim, `Y0Points.lean`); adapted proofs of `exists_oddStep`, `stepSeam_two` and `exists_quotientSeam_of_steps` (`SeamFormula.lean`), each with a provenance line.
- Final SHA: this commit (the commit that adds this file).
