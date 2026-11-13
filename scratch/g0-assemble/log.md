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
- g0-mod-galois over Leaves.lean (part 70): adapted (documented in the part): `G10Glue`'s placeholder
  hypotheses `HSyn.T11_RiemannGAGA → HSyn.T12_ArtinComparison` (opaques removed by leaf-adopt2) replaced by the
  bundle's concrete `ZInQ.LeafPush2.T11a_RiemannEnd → T11b_Rigidity` (T12 is glue since leaf-adopt2);
  bundle-field renames in proofs: `t.t11 t.t12` -> `t.t11a t.t11b`, `t.t18` -> `t.frobeniusDense`,
  `t.t19` -> `HSyn.t19_proved`; `newformG12Out_of_galois` takes `HSyn.KroneckerWeber` as a hypothesis
  (the bundle's `t17` is now the weaker `KroneckerWeberCyclic`; this theorem is not on the assembled route).
- g0-mod-newform over Leaves.lean (parts 72, 77): kernel LadicCond.lean Part B-D copied (part 72);
  `open LeafModCurves hiding ...` as leaf-adopt3 did for C9Rhof (Leaves.lean's `LeafModCurves` has copies
  `Qbar`, `GQ`, `IsArithFrob`, `CF`, `coeff`, `IsNewform`, ...); `ZInQ.Mult.le_heightD_of_mem_S_mul` ->
  `G0ModField.le_heightD_of_mem_S_mul` (verbatim copy; Main.lean not importable: upstream helper
  ZInQ.PoleValuation not built). TailG (74,75,70,72,77): VERIFIED 0 errors, no sorry.
- part 87 (AfterG7 from g0-mod-galois + g0-mod-newform + ModelG3G6 + LinkedTateData): first run: missing `open CategoryTheory AlgebraicGeometry`; second run VERIFIED 0 errors, `HSyn.G0AssembleMod.afterG7_of` standard axioms.
- Tail run (all parts, GluePieces2 with the full modular decomposition): VERIFIED 0 errors, no sorry; afterG7_of, modularConstituent_of_field, gluePieces_of_gluePieces2, sixContactMin_of_leaves2: standard axioms (04:44).
- Flat file `lake env lean scratch/g0-assemble/G0Assemble.lean` (41847 lines, version of commit 'GluePieces2 with ModularConstituent fully decomposed'): VERIFIED exit 0 in 568 s, 0 errors, no sorry, 179 #print axioms lines, all [propext, Classical.choice, Quot.sound].
- G15RamWild refinement (LinkedTateData asks only clauses (i)-(ii); `g15RamG_of_wild` proves G15RamG from them and G11Out): TailG VERIFIED 0 errors, afterG7_of standard axioms.
- Final flat file (41883 lines): VERIFIED exit 0 in 573 s, 0 errors, no sorry, 179 axiom lines all standard (04:55-05:05).
- `HSyn.G0AssembleMod.resQFiniteIndex : G0Galois.ResQFiniteIndex` proved (part 88; primitive element
  `α`, stabilizer of `g⁻¹α` in the range of `resQ K`, orbit inside the roots of the minimal polynomial).
  Run 1: wrong lemma name (`adjoin_simple_toSubalgebra_of_integral` -> `..._of_isAlgebraic`) and a
  `subst` that removed `α`; run 2 VERIFIED, standard axioms. Field `resQFiniteIndex` removed from
  GluePieces2 (now 28 fields). Tail run: 0 errors, standard axioms.
- Final flat file (41970 lines, with resQFiniteIndex): VERIFIED exit 0 in 548 s, 0 errors, no sorry, 180 axiom reports all standard.
