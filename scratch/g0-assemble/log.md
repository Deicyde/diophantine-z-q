# g0-assemble results log

## 2026-11-13
- Copied scratch/h-decomposition/Leaves.lean to scratch/g0-assemble/Leaves.lean (byte-identical, `cmp`).
- Built the upstream helpers: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (ok).
- parts/ (one file per wave-26 task, extracted by line range from the task's compiled file):
  05 bp-analytic Torus+QMLattice (kernel copy, for g0-thetapoint); 10 g0-dim part_dim; 20 g0-product §2-§5
  (G0Split. -> HSyn.G0Split. as in its mkcheck.sh); 30 g0-reverseisog SplitRev.lean tail (G0RevIsog only);
  40 g0-fibresimple tail; 50 g0-stablebc Main.part; 60 g0-heightadd (G0HeightAdd sections); 70 g0-mod-galois
  four parts; 80 g0-thetapoint part_theta (ThetaPt only); 90 the bundle GluePieces2 and the theorems.
- Prefix olean: `build_prefix.sh` compiles Leaves.lean (unchanged) to olean/LPrefix.olean: exit 0 in 605 s.
- Tail run 1: parts 05-60 compile; errors in 60 (an extra `end`: lines 388-389 of part_heightadd are
  `end HSyn`/`end`; range now 390-473) and in 80 (g0-split's copies `HSyn.G0Split.Char2`, `thetaConst`, `CPts`,
  `IsUniformization`, `IsSiegel`, `IsPeriodMatrix`, `absLogHeight` were replaced in Leaves.lean by leaf-push2's
  `ZInQ.LeafPush2` originals (leaf-adopt3); fixed by one `open ZInQ.LeafPush2 (...)` line inside `ThetaPt`; the
  definitions are textually identical, the statements unchanged).
- Moved g0-mod-galois' parts to off/: its `g8_g12_of_leaves` uses the old bundle fields `t.t11`, `t.t12`, `t.t19`
  (Split.lean's bundle) and `G10Glue` takes the opaque placeholders `HSyn.T11_RiemannGAGA`,
  `HSyn.T12_ArtinComparison` as hypotheses; both placeholders were removed from Leaves.lean by leaf-adopt2.
- Tail run 3 (parts 05,10,20,30,40,50,60,80,90): VERIFIED exit 0, 0 errors, no `sorry`;
  `HSyn.gluePieces_of_gluePieces2`, `HSyn.sixContactMin_of_leaves2`: [propext, Classical.choice, Quot.sound].
- g0-mod-field over Leaves.lean (TailMF.lean = LPrefix + 3 non-HDecomp kernel imports + ModField.lean lines
  16-1036): compiles except `GlueWP3.leafHasse_of_T14`, `leafLocalTwo_of_T15` (kernel Descent/WP3.lean, not in
  Leaves.lean); with WP3.lean copied (part 74): VERIFIED 0 errors.
- Layer caveat (g0-mod-newform §3 step 4): `HSyn.abVarEquiv_baseChange`, `abVarEquiv_symm_baseChange` are `rfl`
  (VERIFIED), `HSyn.commonConstituent_copy` is `Iff.rfl`; `HSyn.modularConstituent_of_G :
  G0ModField.ModularConstituentG → G0Split.ModularConstituent` compiles (a direct `exact` of the anonymous
  constructor hit a whnf heartbeat timeout; `refine` + `rw [abVarEquiv_symm_baseChange]` works).
  `HSyn.modularConstituent_of_field t hCover hKer hSup hRest`: VERIFIED, standard axioms.
- Tail run with parts 05-90 incl. 74/75/85 and GluePieces2 using `modularConstituent_of_field`: VERIFIED 0 errors, no sorry, standard axioms for gluePieces_of_gluePieces2, sixContactMin_of_leaves2 (04:33).
