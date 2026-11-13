# linked-tate results log

## 2026-11-13
- Copied scratch/h-decomposition/Leaves.lean (pin-applied, commit base f90cf864) to scratch/linked-tate/Leaves.lean (byte-identical, `cmp`).
- Built upstream helpers: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` + the three
  imports of imports_extra.txt (ok, 9171 jobs). First prefix run failed before that (`unknown module prefix 'ZInQ'`).
- parts/: verbatim copies of scratch/g0-assemble/parts/{70_galois,72_ladiccond,74_wp3,75_modfield,77_newform,87_afterg7}.lean
  (87 holds the target Props `ModelG3G6`, `LinkedTateData`, unchanged); 92_c10link.lean (kernel C10/Link.lean excerpts,
  verbatim); 93_g14.lean (scratch/g14-trace/part_g14.lean excerpts, verbatim); 95_linked.lean (new).
- Prefix olean (`build_prefix.sh`, LPrefix = Leaves.lean + imports_extra): VERIFIED exit 0 in 591 s.
- Tail run 1: errors (kernel excerpt line range cut `trace_T_of_frobCompare`'s last line and a docstring;
  `Module.Free ℚ_[ℓ] (A.V ℓ)` typeclass timeout in `trace_endE_indep`). Fixed: range 150-173, and
  `set_option synthInstance.maxHeartbeats 400000 in` before `trace_endE_indep` (documented in part 92).
- Tail run 2: `endBC` needs `open ... MonObj` (Hom monoid instances). Run 3: `γ` is a notation token after
  `open ... CartesianMonoidalCategory MonObj` (renamed to `gm`).
- Tail run 4: VERIFIED 0 errors, no sorry. Standard axioms [propext, Classical.choice, Quot.sound] for
  HSyn.LinkedTate.{oI_oH_ne, noncomm_baseChange2, endDivision_of_fibreSimple, qmModelG3_of, modelG3G6_of,
  toHom_eq_one_of_intertwines, localRamWild_of_rho, linkedTateCore_of, linkedTateData_of, afterG7_of_linked,
  afterG7_of_linked'} and the copied HSyn.G0AssembleMod.afterG7_of.
  Statements: `modelG3G6_of (hFS : G0Split.FibreSimple) (hG3 : QMModelG3) : ModelG3G6`;
  `qmModelG3_of (r7a) (r6) (t5) (hB : GoodRedG3Bridge) : QMModelG3`;
  `linkedTateData_of (hM : PkgI3.CharPolyIndepOfEll) (hC : LinkedTateCore) : LinkedTateData`;
  `linkedTateCore_of (hFS) (hR : QMEndRank) (hDR : LinkedTateCoreDR) : LinkedTateCore`.
- Part 96: scratch/unram-tate/TateBridge.lean lines 1038-1825 copied verbatim (plus the file-level opens of
  ModField.lean). Tail run: VERIFIED 0 errors; `UnramTate.tateBridge_of_tateModuleFree` standard axioms (g0-mod-field's
  `TateBridge` from I3.M0, now compiled over Leaves.lean too).
- Part 97 (new): `UnramTate.scalarTransferQ` (unram-tate's scalarTransfer with target ℚ̄), `UnramTate.tmOf` (canonical
  operators), glue Prop `UnramTate.LinkedFrobRam`, `UnramTate.linkedTateCoreDR_of (hT : TateModuleFree) (hFR :
  LinkedFrobRam) : LinkedTateCoreDR`, `HSyn.LinkedTate.linkedTateData_of_frobRam (t7) (I3.M0) (FibreSimple) (QMEndRank)
  (LinkedFrobRam) : LinkedTateData`. First run VERIFIED 0 errors, no sorry, all standard axioms.
- `LinkedFrobRam` split into `UnramTate.LinkedFrob` (FrobTraceLink for `tmOf`, no γ₀/j quantifiers) and
  `UnramTate.LinkedRam` (RhoRamWild); `linkedFrobRam_of` proved. Composite `HSyn.LinkedTate.afterG7_of_final
  (r t m hDF hCar hSw hL8 hAd) (FibreSimple) (GoodRedG3Bridge) (QMEndRank) (LinkedFrob) (LinkedRam) : AfterG7`.
  Tail run: VERIFIED 0 errors, all standard axioms.
- Flat file `lake env lean scratch/linked-tate/LinkedTate.lean` (40891 lines; parts 10,70,72,74,75,77,87,92,93,95,96,97):
  VERIFIED exit 0 in 592 s, 0 errors, no sorry, 208 `#print axioms` reports, all [propext, Classical.choice, Quot.sound]
  (two are line-wrapped in the output).
- All g0-assemble parts copied (05,20,30,40,50,60,80,85,88,89,90 added). Tail run 1: one error, in part 40
  (g0-fibresimple's §5 `r1fpProps_twistBy`: its `obtain ⟨hp, hs, hq, hnat⟩` fails against the pin-applied
  `R1fpProps`, as pin-apply intended). §5 (`PtAuto` ... `fibreComTrivial_twisted`, unused elsewhere) removed from the
  copy, with a note in the part.
- Part 98: `tate_eq_one_of_torsion` (proved), glue `GoodRedTorsion`, `goodRedG3Bridge_of_torsion` (proved).
- Part 99: `HSyn.GluePieces3` (GluePieces2's 25 fields before `modelG3G6`, verbatim, + goodRedTorsion, qmEndRank,
  linkedFrob, linkedRam), `gluePieces2_of_gluePieces3`, `sixContactMin_of_leaves3 r t gp3 : ZInQ.SixContactMin`.
  Tail run 2 (10212 lines): VERIFIED 0 errors, no sorry; `sixContactMin_of_leaves2`, `gluePieces2_of_gluePieces3`,
  `sixContactMin_of_leaves3`, `afterG7_of_final`, `goodRedG3Bridge_of_torsion`: standard axioms.
- Flat file (44818 lines: all g0-assemble parts, 92-99 with GluePieces3 using goodRedTorsion and linkedRam):
  VERIFIED exit 0 in 590 s, 0 errors, no sorry, 217 axiom reports all standard, incl. `HSyn.sixContactMin_of_leaves3`.
