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
