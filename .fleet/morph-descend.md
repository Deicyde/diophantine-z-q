# morph-descend: fleet summary

**Verdict: G4's input `MorphismsDescend` (EGA IV₃ 8.8.2 for `ℚ̄ = colim L`) is proved in Lean.**
The proof has no hypotheses, no `sorry`, and only the standard axioms. So `MorphismsDescend` is
no longer a leaf; it is glue.

- **Main result:** `MorphDescend.morphismsDescend : MorphismsDescend` in
  `scratch/morph-descend/Descend.lean`, 404 lines.
  - Its imports are Mathlib and `ZInQKernel.HDecomp.Objects`.
  - The statement is copied verbatim from `scratch/g4-weilres/G4.lean`; `diff` shows the two are
    identical.
  - It compiles with 0 errors and 0 warnings.
  - `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- **The geometric input is already in Mathlib:**
  `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` in
  `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`. It is the surjectivity half of Stacks
  01ZC: a morphism from a cofiltered limit of qcqs schemes with affine transition maps to an LFP
  scheme factors through a finite stage.
- **The glue proved here:**
  - `ℚ̄` is the filtered colimit of its number subfields containing `E₀` (in `CommRingCat`);
  - so `Spec ℚ̄ = lim Spec L` in `Over (Spec K)`;
  - so `X ×_K ℚ̄ = lim X ×_K L`, with affine transition maps and qcqs terms;
  - the general `exists_descend`, for `X` qcqs and `Y` LFP over any field `K`;
  - the instance for `PkgI3.AbVar` (proper ⇒ qcqs, smooth ⇒ LFP).
- **Also compiled:** `scratch/morph-descend/G4Closed.lean`. It is G4.lean, unchanged, with this
  proof prepended, and adds three theorems:
  - `G4WeilRes.morphismsDescend`;
  - `G4WeilRes.homDescends`, so the continuity input is now unconditional;
  - `G4WeilRes.homField_of_model_closed`: the G4 headline without the `MorphismsDescend` argument.

  All printed axioms are standard.
- **What remains of G4:** the leaf `PkgI3.HomFreeFinite`, the input `InertiaFixesHoms`, and the
  hypotheses `hK` (G2), `hgood` (G3) and `hdim`. None of these is in scope here.
- **Report:** `docs/research/morph-descend.md`. **Log:** `scratch/morph-descend/log.md`.
