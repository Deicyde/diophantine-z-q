# height-glue (fleet report)

**Main result (VERIFIED, compiled, standard axioms).** height-split's whole glue bundle `HeightGlue`
follows from the textbook leaf T35 (`LeafPush2.UniformizationExists` = `TextbookLeaves.t35`), with
no new leaf: `heightGlue_of_t35`. In detail:
- kernel `AnalyticUniformizationUnique` is proved from the kernel's own `AnalyticUniformizationExists`
  (`analyticUniformizationUnique_of_exists`): analytic topology on `𝒢(ℂ)_τ`, its Hausdorffness
  (proved, no hypotheses), immersion at `0` of every discrete-kernel uniformization (proved),
  covering-space lift through `ℂ^g/Λ`, linearity, Baire, linear algebra;
- `MetrizationOfUniformization` proved with no hypotheses; `UniformizationDim` and
  `NeronMetrizable` from T35;
- `Rows.lean`: `heightRows_of_t35 : HeightLeaves → T35 → R18 ∧ R19 ∧ R20 ∧ R21 ∧ R22 ∧
  StableHeightFinite`.

**H-3.** `QMPairEmbeddingCorrespondence` follows from two leaves
(`qmPairEmbeddingCorrespondence_of_leaves`):
- `QMUniformizationC`: Shimura's moduli of QM surfaces over ℂ (classes ≃ `𝒪^× \ (ℂ∖ℝ)`,
  `End_𝒪 ≅ 𝒪_τ`);
- `QMDescentCM`: base change from `ℚ̄`, rigidity, CM descent.

The glue between them, `CMPointEmbeddingCorrespondence` (CM points ↔ optimal embeddings, through
normalized embeddings), is **proved** with no hypotheses (`QMEmb.lean`). It uses an explicit
`rho : B → M₂(ℂ)`, eigenvector lemmas, the centralizer of a non-scalar element of `B`, `liftQuad`
for the quadratic field, and conjugation-stability of orders. An independent statement review found
no defect in the QM Props.

**Compiles:** `scratch/height-glue/{AUUnique,HeightGlue,Rows,QMCorr,QMEmb}.lean` (`lake env lean`, exit 0,
no `sorry`, standard axioms).
**Remains:** the two QM leaves (see report §5 for how they could be split further). Report:
docs/research/height-glue.md; log: scratch/height-glue/log.md.
