# glue-assembly: results log

Task: glue clusters C8, C10, E1, E3, E4, F2 of `docs/research/h-trust.md`; Lean proofs of the
elementary parts in `scratch/glue-assembly/`. Marks: VERIFIED (read in a source, computed, or
compiled), STANDARD (published, exact reference), SPECULATIVE. Theorem numbers recalled from memory
are UNVERIFIED.

## Step 0 (start, 2026-11-11)

- No earlier run (no log). Branch `wip/glue-assembly` at a4355d3e.
- Sources read: h-trust §0-§1 C1-F4; N5 L377-403 (constants), L578-631 (CM branch), L719-800
  (C1-C10), L855-972 (D5-F4); wk-h §§1-6 (with `scratch/wk-h/Arakelov.lean`, whose
  `transfer_numerics` already proves the E3-E4 arithmetic as a real lemma);
  `ZInQKernel/Hypotheses/{Height,HeightMin,JHeight}.lean`.
- VERIFIED (ls): `.lake/build/lib/lean/ZInQKernel/Hypotheses/JHeight.olean` exists in this
  worktree, so scratch files can `import ZInQKernel.Hypotheses.JHeight` (unlike wk-h's worktree).
- VERIFIED (read Mathlib v4.35 `NumberTheory/Height/{Basic,MvPolynomial,NumberField}.lean`):
  `Height.logHeight` (projective, relative to `K`, with `AdmissibleAbsValues`),
  `logHeight_eval_le` (degree-`N` homogeneous map, explicit `mulHeightBound`),
  `logHeight₁_div_eq_logHeight`, `NumberField.mulHeight_eq`, `totalWeight_eq_finrank`,
  `Rat.logHeight₁_eq_log_max`. No lemma relating `logHeight₁ (algebraMap ℚ K q)` to the height of
  `q` over `ℚ` (the "height invariance under extension" that wk-h §4.2 flagged).
