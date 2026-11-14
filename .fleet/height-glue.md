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

**H-3.** The row `R5fpCount` follows from height-split's Eichler leaf, the kernel's textbook leaf
`T11b_Rigidity` and two new leaves (`r5fpCount_of_t11b`):
- `CMDescent` (Shimura–Taniyama: CM QM pairs over ℂ come from `ℚ̄`);
- `QMUniformizationC` (Shimura: QM pairs over ℂ ≃ `𝒪^× \ (ℂ∖ℝ)` with `End_𝒪 ≅ 𝒪_τ`).

Proved on the way:
- `CMPointEmbeddingCorrespondence` (CM points ↔ optimal embeddings through normalized embeddings;
  explicit `rho : B → M₂(ℂ)`, eigenvector and centralizer lemmas, `liftQuad`, conjugation-stable
  orders);
- base change of QM pairs (`bcPair`), with `End_𝒪` and isomorphisms preserved via T11b.

An independent review found no defect in the QM Props of the first route (`CMDescent` not
reviewed).

**Compiles:** `scratch/height-glue/{AUUnique,HeightGlue,Rows,QMCorr,QMEmb,QMFull}.lean` (`lake env lean`, exit 0,
no `sorry`, standard axioms).
**Remains:** the leaves `CMDescent` and `QMUniformizationC` (report §5 sketches a further split of the latter). Report:
docs/research/height-glue.md; log: scratch/height-glue/log.md.
