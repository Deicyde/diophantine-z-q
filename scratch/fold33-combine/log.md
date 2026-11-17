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
3. goodmodel-iso (894fb85b, fold G: `mumfordGroupLawConn` and `neronSchemeExtensionExists` → `neronSchemeExtensionDedekind`):
   applied by `scratch/fold33-combine/gm_fold.py` (asserts every edit), on top of step 2.
   - Research side, in place (G.patch's edits): `mumfordGroupLaw : MumfordRigidity.MumfordGroupLaw` narrowed to
     `GroupLaw.MumfordGroupLawDVR` in `OpenResearchLeaves14`–`27` (14 structures; a two-line comment before each);
     TailZ23 imports `MumfordGroupLawRed`, its three `qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw` become
     `qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw`; TailZ34's `y3Connected_of_leaves r.mumfordGroupLaw …` becomes
     `y3Connected_of_ab_gl (qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw) (y3ConnectedAb_of_U …)`; TailZ45 imports
     `NeronGoodModelIso`, `OpenResearchLeaves28`'s field `mumfordGroupLawConn` becomes `neronSchemeExtensionDedekind`
     (G's docstring) and `mumfordGroupLaw := GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`.
     On this base the same swap is also needed in `OpenResearchLeaves29` (TailZ46, leaf-fold33's autofold generation,
     which did not exist on c1e4ed1b): field and pass-through line.
   - Textbook side, not in place: G's new `OpenTextbookLeaves14` (on c1e4ed1b) is re-expressed as a new top module
     `OneProof/H/TailZ49.lean` over leaf-fold33b's TailZ48 (autofold's shape, written by the script):
     `OpenTextbookLeaves16` = `OpenTextbookLeaves15` without `neronSchemeExtensionExists`;
     `openTextbookLeaves15_of_OpenTextbookLeaves16 (n) (h : NeronSchemeExtensionDedekind)` with
     `neronSchemeExtensionExists := neronSchemeExtensionExists_of_dedekind h`;
     `sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves20)` :=
     `sixContactMin_of_open41 r (openTextbookLeaves15_of_OpenTextbookLeaves16 t r.neronSchemeExtensionDedekind) l`.
     Main imports TailZ49 and calls `sixContactMin_of_open42 r t l` with `t : OpenTextbookLeaves16`; Main's module
     docstring has a fold33-combine paragraph. The homfree copies of the textbook chain are untouched by this side.
   - homfree reroute regenerated (taint output identical to step 2's except the closure size; 39 + 96 blocks): the
     copies `x6Rows_of_open14_hf`, `researchLeaves9_of_open14_hf` and `sixContactMin_of_open28_hf` take the new readers.
   - kinds.tsv: rows `mumfordGroupLawConn` and `neronSchemeExtensionExists` dropped, row `neronSchemeExtensionDedekind`
     added (research, published, LEAF/LEAF, flag from goodmodel-iso's fold/autofold-G.json "locator UNVERIFIED (BLR,
     Neron models, 1.4 Thm 3 with 1.2 Def 1, existence half, affine Dedekind base)", flag class unverified-locator,
     packet R2 and area issue #85 as the textbook row it absorbs, tier T4, rated_by "goodmodel-iso spec; fold33-combine;
     pending review"). claims.tsv: the two held project rows (group-law, neron-ext) dropped.
   Checks (VERIFIED):
   - `lake build +Main +Discharges ZInQKernel` and every `ZInQKernel/Contrib/OneProof/*.lean` module (includes
     NeronGoodModelIso, MumfordGroupLawNeron, MumfordGroupLawRed): 14269 jobs, 0 errors.
   - `#print axioms ZInQ.OneProof.frozenTarget` and `HDec.HSyn.sixContactMin_of_open42`: [propext, Classical.choice, Quot.sound].
   - Closure (closure_2_gm.txt): 270400 constants; no `DictModels.MumfordConn.MumfordGroupLawConn`,
     `mumfordGroupLaw_of_conn`, `MumfordRigidity.MumfordGroupLaw`, `qmFamilyGroupLaw_of_groupLaw` (and none of step 2's
     SGA 3 names, no HomFree, no sorryAx); `NeronSchemeExtensionDedekind`, `mumfordGroupLawDVR_of_dedekind`,
     `neronSchemeExtensionExists_of_dedekind` are in it. `NeronC.NeronSchemeExtensionExists` stays in the closure as a
     proved intermediate statement (its consumers take it as an argument), as goodmodel-iso's §5 says; no bundle field
     of frozenTarget has it as type (textbook bundle `OpenTextbookLeaves16`: 3 fields).
   - Hash guard (hashes_1_sga3.txt → hashes_2_gm.txt, hashdiff_2_gm.txt): before 14091, after 14102; only before 2
     (`OpenResearchLeaves28/29.mumfordGroupLawConn`); only after 13 (`OpenResearchLeaves28/29.neronSchemeExtensionDedekind`
     and TailZ49's 11 constants); changed 100, all explained: the 16 structures `OpenResearchLeaves14`–`29` change a
     field type, so `mk`, `mk._flat_ctor`, `rec`, `casesOn`, `recOn` change (80); the projection `mumfordGroupLaw` of
     `OpenResearchLeaves14`–`27` changes type (14); `openResearchLeaves27_of_28` (new supplier) and `28_of_29` (renamed
     pass-through) change value; the readers `x6Rows_of_open14`, `researchLeaves9_of_open14` (TailZ23) and
     `sixContactMin_of_open28` (TailZ34) change value; `ZInQ.OneProof.frozenTarget` changes type and value (binder
     `OpenTextbookLeaves16`, calls `_open42`).
   - OpenStatements: 41 open hypotheses.
   - `render_open.py` then `--check`: ok, 41 open hypotheses, all classified; **31 H hypotheses, strictest 11/20**,
     10 others (32, 12/20 before: −2 LEAF fields + 1 LEAF field).
   - `frontier_crosswalk.py` regenerated (31 matched; `neronSchemeExtensionDedekind` has no frontier ID), `--check` ok.
   - DischargesTest rerun.
   - Blueprint (not editable here; autoform not installed on this host, so not run): two pages name Lean targets that
     the in-place folds delete: blueprint/roadmap/height-decomposition/abelian-varieties/mumford-group-law.md
     (`HDec.HSyn.OpenResearchLeaves28.mumfordGroupLawConn`) and group-schemes/identity-component-neighbourhood.md
     (`HDec.HSyn.OpenResearchLeaves28.sga3_VIB_3_10_Nbhd`). `autoform render --require-declarations` will report them
     until the blueprint retargets or drops them (the other `\lean`/`lean:` targets checked by grep still exist:
     `OpenTextbookLeaves13.neronSchemeExtensionExists`, `.charPolyIndepOfEllAlgClosed`, `.poincareComplement`).
