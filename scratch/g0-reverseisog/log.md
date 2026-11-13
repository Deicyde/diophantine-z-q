# g0-reverseisog results log

- Source of the piece: `scratch/g0-split/Split.lean` on branch `wip/g0-split` (c20fa62b), not in the
  base 883c4ddf; read with `git show origin/wip/g0-split:scratch/g0-split/Split.lean`.
- `scratch/g0-reverseisog/ReverseIsogeny.lean`: Mathlib-only file; §1-2 verbatim copies of
  `PkgI3.AbVar` (+dim, homGroup, Hom, IsIsogenyMor), def-faltings `AbVar`, `AbVar.dim`, `IsIsogeny`,
  `LeafAdopt.abVarEquiv`, `G0Split.IsProductOf`, `G0Split.ReverseIsogeny`.
- §3: leaf `G0RevIsog.IsogenyQuasiInverse` (Mumford/Milne quasi-inverse of an isogeny, numbers
  UNVERIFIED); glue proved: `lift_series`, `topologicalKrullDim_le_of_specializing`,
  `dim_le_of_finite_surjective`, `dim_eq_of_isogenies`, `isogeny_of_product`;
  `reverseIsogeny : IsogenyQuasiInverse → G0Split.ReverseIsogeny`.

## Compile outcomes (VERIFIED)

- 01:52 `lake env lean ReverseIsogeny.lean`: 0 errors (after adding `noncomputable section` and
  stating `isogeny_of_product` with codomain `J.X`). `#print axioms G0RevIsog.reverseIsogeny`,
  `G0RevIsog.topologicalKrullDim_le_of_specializing`: `[propext, Classical.choice, Quot.sound]`.
  Sanity `example`: `(𝟙 A.X) ^ 2 = lift (𝟙 A.X) (𝟙 A.X) ≫ μ[A.X]` by `pow_two; rfl` (the leaf's
  `[n]` is the group-object multiplication by `n`).
- Restructured: interface `IsogenyReverseExists` (number fields, existence of an isogeny back);
  `reverseIsogeny_of_exists : IsogenyReverseExists → ReverseIsogeny`;
  `isogenyReverseExists_of_quasiInverse`.
- `SplitRev.lean` = `Split.lean` (first 20024 lines byte-identical, `diff` empty) + §3″:
  Route B `isogenyReverseExists_of_r19 (R19_GaudronRemond) (StableHeightFinite) (DimFinite)`,
  `reverseIsogeny_of_leaves (r : ResearchLeaves) (DimFinite)`, `glueOutputs_of_leaves_rev`
  (nine pieces), `MissingPiecesRev`, `sixContactMin_of_leaves_rev`. Needed
  `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` first
  (11 s, replay). 01:59 `lake env lean SplitRev.lean`: exit 0, 0 errors, no `sorry`, 2m57s;
  `#print axioms` of `HSyn.G0RevIsog.reverseIsogeny`, `HSyn.G0RevIsog.reverseIsogeny_of_leaves`,
  `HSyn.glueOutputs_of_leaves_rev`, `HSyn.sixContactMin_of_leaves_rev`: standard three.
