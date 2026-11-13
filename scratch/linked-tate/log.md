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
- Part 98b: `UnramTate.tmOf_resQ` (proved), glue `KernelFieldBreaks`, `LocalInertiaGlobal`, `UpperAbsInertia`,
  `TateRamAtThree`, `tate_trivial_of_g3`, `linkedRam_of (QMModelG3) (KernelFieldBreaks) (LocalInertiaGlobal)
  (UpperAbsInertia) (TateRamAtThree) : LinkedRam`. Run 1: a `rw` failed on an unreduced beta-redex (`gam (h*g*h⁻¹)`);
  fixed with `show`. Run 2: VERIFIED 0 errors, no sorry; `linkedRam_of`, `sixContactMin_of_leaves3` standard axioms.
  GluePieces3 now has 32 fields (field `linkedRam` replaced by the four Props).
- `LocalInertiaGlobal` PROVED: standalone over Mathlib first (scratch/linked-tate/test/LocalInertia.lean; run 1: three
  lemma-name fixes `inv_le_one₀`, `Padic.norm_p`, `IsLocalRing.ResidueField.residue_smul`; run 2 clean), then as part
  98c (`UnramTate.embP`, `embP_decomp`, `localInertiaGlobal_at`, `localInertiaGlobal`). Tail: VERIFIED 0 errors,
  standard axioms; GluePieces3 field `localInertiaGlobal` removed (31 fields); `sixContactMin_of_leaves3` standard.
- `UpperAbsInertia` PROVED: standalone over Mathlib (scratch/linked-tate/test/UpperAbs.lean; fixes: `IntermediateField.
  normalClosure` with explicit args), then part 98d (`phiAt_nonpos`, `sInf_nonneg_of_pos`, `upperSet_sub`,
  `upperAbs_subset_inertiaSet'`, `upperAbsInertia`). Tail: VERIFIED 0 errors, standard axioms; GluePieces3 field removed
  (30 fields); `sixContactMin_of_leaves3` standard.
- FINDING (by reading N5 L805-852 and g0-mod-field's G7Data): `G7Data` omits `[L:ℚ] ≤ D` (G4Out has it). Two
  consequences for this task's glue: (1) `LinkedRam` quantified over every γ₀ is false for oversized L (twist by a
  character of Gal(L'/ℚ) of large conductor at 2), so γ₀ is now tied to G7Data's β/a by an embedding κ : ℚ̄ → ℂ;
  (2) `KernelFieldBreaks` (and `TateRamAtThree` for large K) are only justified under [L:ℚ] ≤ D (SPECULATIVE
  counterexample: L ⊇ ℚ(ζ_{2^k}), k > U₀+1, when M_{S_mul}(u) is large). Changes: `scalarTransferQ` now also returns
  κ with κ(γ₀ σ) = β σ / a σ (preimages under κ of the algebraic values, injectivity); tie hypothesis added to
  `LinkedFrobRam`, `LinkedRam`; GluePieces3 keeps `linkedRam` (fields kernelFieldBreaks, tateRamAtThree removed; 29
  fields); part 98b kept as a conditional reduction with a caveat note.
  Tail: VERIFIED 0 errors, no sorry; scalarTransferQ, linkedTateCoreDR_of, linkedRam_of, sixContactMin_of_leaves3 standard.
- Flat file (45120 lines, final parts incl. γ₀ tie, GluePieces3 with 29 fields; one later comment-only edit in part 98b):
  VERIFIED exit 0 in 542 s, 0 errors, no sorry, 222 axiom reports all standard, incl. `HSyn.sixContactMin_of_leaves3`.
