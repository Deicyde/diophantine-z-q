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

**H-3.** `QMPairEmbeddingCorrespondence` reduced to two leaves (`QMUniformizationC`, Shimura's
moduli of QM surfaces over ℂ; `QMDescentCM`, base change/rigidity/CM descent) and one glue
(`CMPointEmbeddingCorrespondence`, normalized optimal embeddings), with explicit `rho : B → M₂(ℂ)`,
`cmSetoid`, `ordAt` (QMCorr.lean).

**Compiles:** `scratch/height-glue/{AUUnique,HeightGlue,Rows,QMCorr}.lean` (`lake env lean`, exit 0).
**Remains:** the glue `CMPointEmbeddingCorrespondence` and the two QM leaves. Report:
docs/research/height-glue.md; log: scratch/height-glue/log.md.
