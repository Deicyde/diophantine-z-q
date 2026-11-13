# leaf-adopt (2026-11-12)

**Result.** `scratch/h-decomposition/Leaves.lean` now states **48 of the 56 leaves** concretely.
R1 is concrete in parts (a), (c) and (d), with the new clause `π₀(X₆)=1`. Only **7 leaves** (R3,
R17, R18, R22, T10, T11, T12) and **R1(b)** are still `opaque`. Before this task the count was 40
concrete and 14 placeholders out of 54.

**What changed.**
- **Concrete now:** R1(a, c, d), R2 and R5 (from leaf-qm-fp), R16 (from leaf-modcurves), and
  R19-R21 over `stableFaltingsHeight` (from def-faltings).
- **New leaves:** H5 (research level), and T33 `JacobianExists` and T34 `DimJ1Genus` (textbook).
- **T32 is now glue.** Both parts are proved in `HSyn.t32a_glue` and `HSyn.t32b_glue`, using
  glue-t32a and glue-b3b, so it is no longer a leaf.
- **rv-blueprints repairs applied:**
  - Q2: `R5fp ↔ R5fpStrong` is proved.
  - Q3: R1(b) is restated in family form; it stays a placeholder.
  - Q4: `π₀(X₆)=1` is added as a leaf clause.
  - Q5: the biconditional CM clauses are proved as glue.
  - M1: R16 is stated for every `K_N` model, so MC9 is dropped as a leaf.
  - F2: H5 is now an explicit leaf.
  - F1: the claim that additivity of the height follows from its definition is corrected in the
    note.
- **Glue:** no glue step used a replaced placeholder, so no glue statement changed.

**What compiles.** `lake env lean scratch/h-decomposition/Leaves.lean` exits 0 in about 2.5-3.5
minutes (19.2k lines).
- One `sorry`, the same as before: `HSyn.glueOutputs_of_leaves`.
- 8 `opaque` declarations and no `axiom`.
- Every `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound`, except
  `sixContactMin_of_leaves`, which also depends on `sorryAx`.
- The four report files are copied verbatim as sections, because their kernel imports clash with
  namespaces already defined in `Leaves.lean`. The only change to a statement is one renaming in
  the copy of leaf-qm-fp.

**Caveats.**
- The Shimura-curve leaves (R1, R2, R5) hold only together with the SPECULATIVE premise
  bp-qmmoduli §2.2 (the polarization exists and is unique).
- The height leaves (R19-R21, H5) are not yet known to be non-vacuous. The three Props of AN3
  (two on analytic uniformization, plus `HodgeLatticeTheorem`) are still open.
- An independent model review found no defect, and listed risks (R19's normalization, R20's
  unread locator, R1's PEL specialization). It was a model review, not a human one.

**Remaining.**
- The 8 placeholders, including folding in R17 from def-ladic-cond.
- The §2.2 premise and AN3.
- The glue targets `X1ModelExists`, `BelyiX1` and `VSurjOfSurjective`.
- Unifying the duplicate abelian-variety layers (WP1).
- `glueOutputs_of_leaves`.

Report: `docs/research/leaf-adopt.md`; log: `scratch/leaf-adopt/log.md`.
