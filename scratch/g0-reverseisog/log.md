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
