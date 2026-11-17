# fold33-combine log

Base: wip/leaf-fold33b 0e3c3125 (TailZ48, `sixContactMin_of_open41`; 33 H, strictest 13/20). origin/main c1e4ed1b is
already an ancestor of the base (no merge of main needed).

0. Merged origin/wip/sga3-nbhd (ac9ad381) and origin/wip/goodmodel-iso (894fb85b; it carries group-law, group-law-dvr
   and neron-ext). Clean merges. Scratch files that redeclare HDec.HSyn bundle structures renamed `.lean.txt`
   (content unchanged): scratch/sga3-nbhd/fold/TailZ46.lean (declares `HDec.HSyn.OpenResearchLeaves29` and
   `sixContactMin_of_open39`, which the base already has), scratch/sga3-nbhd/fold/FoldCheck.lean,
   scratch/neron-ext/AutofoldDry.lean (declares `OpenTextbookLeaves13`). Host paths in the merged logs, patches and
   overlay scripts replaced (worktree names; `cd "$(git rev-parse --show-toplevel)"` in the scripts).
   wip/charpoly-charp is not merged (see step 1).
1. charpoly-charp (512080e4, `charPolyIndepOfEllAlgClosed`): **left out, does not compose** (VERIFIED by reading).
   Its reroute replaces TailK's `G0AssembleMod.linkedTateData_of_local t.t7 …` by
   `linkedTateData_of_local_homFree t.t6 (tateModuleFree_of_t5' t.t5) …`: `common_trace_of_homFree (hH :
   PkgI3.HomFreeFinite)` applies Mumford §19 Thm 3 at FrobTraceLink's reduction `Ā` over a field `k` of characteristic
   `p` (docs/research/charpoly-charp.md §1–2). On this base `t6` no longer carries `PkgI3.HomFreeFinite`: homfree-noemb's
   reroute (leaf-fold33 step 8) removed `homFreeFiniteAlgClosed` by giving every T6 reader `HomFreeC.HomFreeFiniteC`
   (fields with a ring hom `k →+* ℂ`, proved from `uniformizationLeafAll_proof` and `mumfordTorsionAlgClosed`); a
   characteristic-`p` field has no such hom. So on this base the charpoly-charp fold needs T6 back in characteristic
   `p` (e.g. homfree-proof's `HomFreeFiniteAlgClosedNoEmb`, Mumford §19 Thm 3 over algebraically closed fields with
   no embedding into ℂ), which makes it a swap `charPolyIndepOfEllAlgClosed` (§19 Thm 4) → a restriction of §19
   Thm 3: count-neutral (33 → 33), not a removal. Regenerating the homfree reroute over the in-place edit would also
   fail by type (`gluePieces_of_open4_hf` would pass `t6 : HomFreeFiniteC` to `linkedTateData_of_local_homFree`).
   Not applied; wip/charpoly-charp not merged.
2. sga3-nbhd (ac9ad381, `sga3_VIB_3_10_Nbhd`): applied as an **in-place prune**, not as sga3-nbhd's copy bypass
   (its gen_fold.py copies the research chain TailZ23–45 into `HDec.HSyn.NOL`; the homfree reroute copies the textbook
   chain, and the two copies would need a copy of their product). Script `scratch/fold33-combine/sga3_prune.py`
   (asserts every edit; 17 H files):
   - field `sga3_VIB_3_10` deleted (with its docstring, replaced by a comment) from `OpenResearchLeaves14`–`26`
     (TailZ23, 25–29, 33–38, 41) and `sga3_VIB_3_10_Nbhd` from `OpenResearchLeaves27`–`29` (TailZ44–46), with the
     pass-through lines;
   - the five readers of sga3-nbhd's FOLD-SPEC table replaced in place: TailZ33 `sga7_IX_3_3 :=
     SGA3Nbhd.NF.sga7_IX_3_3_of_SH' …`, TailZ41 `semistablePersistsSHcp := SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH'
     …`, TailZ44's conversion line `sga3_VIB_3_10 := sga3_VIB_3_10_of_nbhd …` deleted, TailZ45 `sga7_IX_3_3_SH :=
     SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre' …` (TailZ33, 41, 45 import SGA3NbhdDVR);
   - TailZ23's reader (`researchLeaves9_of_open14`, `semistableNeronBaseChange := semistableNeronBaseChange_of_printed_full
     r.blr_1_2_4 r.sga3_VIB_3_10 …`) cannot import `SemistableNeronBaseChangeNoSGA3` (its import closure contains
     TailZ23 and TailZ24, VERIFIED by an import-closure scan), so it becomes a binder `hNBC :
     ZInQ.HeightSplit.SemistableNeronBaseChange`, threaded through `sixContactMin_of_open17` (TailZ23) and `_open18`
     (TailZ24) and supplied in `sixContactMin_of_open19` (TailZ25, which imports the contribution) by
     `SGA3Nbhd.semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 t.geomConnOfRationalPoint` (theta-fold2's
     pattern for `hθ`). Signatures of `_open19` and above unchanged; no other caller of `_open17`, `_open18`,
     `researchLeaves9_of_open14` outside the homfree copies (grep).
   - Docstrings: TailZ25's module note; `sga7_IX_3_3_SHpre`'s docstring in `OpenResearchLeaves28`/`29`.
   - homfree reroute regenerated: `scratch/fold33-combine/hf/Taint.lean` (homfree-noemb's Taint.lean with root
     `HDec.HSyn.sixContactMin_of_open40`, importing TailZ47, so that it runs without the reroute) and
     `scratch/fold33-combine/hf/gen/gen.py` (homfree-noemb's generator, taint file and top module as arguments).
     Sanity check on the unedited base: taint output equal to homfree-noemb's up to the `Main` line, and the generator
     reproduces both reroute files byte for byte (VERIFIED). After the prune: 63 tainted, the same carriers, 39 + 96
     blocks; the reroute file changes only in the copies of the edited declarations (`researchLeaves9_of_open14_hf`,
     `sixContactMin_of_open17_hf`/`18_hf`/`19_hf`, the research conversions 19←20, 20←21, 21←22, 23←24, 25←26 and line
     numbers in `-- copied from` comments); Consumers.lean unchanged.
   - kinds.tsv: row `sga3_VIB_3_10_Nbhd` dropped (no claims row).
   Checks (VERIFIED):
   - `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +…SGA3NbhdDVR +…SemistableNeronBaseChangeNoSGA3`:
     OK (14166 jobs); also `lake build ZInQKernel` plus every module `ZInQKernel/Contrib/OneProof/*.lean` (14265 jobs,
     0 errors; X0ModuliUsed, SGRFold, ThetaWeierstrass8 etc. compile unchanged).
   - `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound].
   - Closure (`ClosureCheck.lean`, closure_1_sga3.txt): 270262 constants; no `CToPrinted.SGA3_VIB_3_10`,
     `SGA3IdComp.SGA3_VIB_3_10_Nbhd`, `sga3_VIB_3_10_of_nbhd`, `idComp_baseChange`,
     `semistableNeronBaseChange_of_printed_full`, `HomFreeFiniteAlgClosed`, `PkgI3.HomFreeFinite`, `sorryAx`;
     `SGA3Nbhd.semistableNeronBaseChange_noSGA3` is in it. `OpenResearchLeaves29` has 24 fields.
   - Hash guard (hashes_0_base.txt → hashes_1_sga3.txt, list in hashdiff_1_sga3.txt): before 14107, after 14091; only
     before 16 (the projections `OpenResearchLeaves14..26.sga3_VIB_3_10`, `27..29.sga3_VIB_3_10_Nbhd`); only after 0;
     changed 239, all explained: the 16 structures `OpenResearchLeaves14`–`29` lose a field, so their constructor
     family changes (64 `mk`/`rec`/`casesOn`/`recOn`/`noConfusion`/… and 16 `mk._flat_ctor`) and the 140 projections
     after the deleted field change value (index shift); the 15 conversions `openResearchLeaves(k)_of_(k+1)`, k = 14..28,
     change value (one field line fewer, or a reader replaced); `researchLeaves9_of_open14`, `sixContactMin_of_open17`,
     `_open18` change type and value (binder `hNBC`); `sixContactMin_of_open19` changes value (supplies `hNBC`).
     `ZInQ.OneProof.frozenTarget` is unchanged (its binder `OpenResearchLeaves29` keeps its name).
   - `lake env lean scripts/one_proof/OpenStatements.lean`: 42 open hypotheses (43 before).
   - `render_open.py` then `--check`: ok, 42 open hypotheses, all classified; **32 H hypotheses, strictest 12/20**,
     10 others (33, 13/20 before).
   - `frontier_crosswalk.py` regenerated (tsv unchanged: the field had no frontier ID), `--check` ok.
   - `scratch/contrib-kit/DischargesTest.lean` rerun into its output file.
