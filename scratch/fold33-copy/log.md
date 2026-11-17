# fold33-copy log

Base wip/leaf-fold33b 30674d98 (origin/main c1e4ed1b is an ancestor: not merged).

## Step 0: merge
- Merged origin/wip/sga3-nbhd and origin/wip/goodmodel-iso; applied fold33-combine aac7b2a6's hygiene diff (scratch bundle copies renamed .lean.txt: scratch/sga3-nbhd/fold/TailZ46.lean, FoldCheck.lean, scratch/neron-ext/AutofoldDry.lean; host paths removed from merged logs/scripts). VERIFIED: the merged scratch/ and ZInQKernel/ trees equal aac7b2a6's on those paths.

## Build tree
- `.lake/build` and `lean/.lake/build` copied (reflink) from the etaw32-proof worktree (same H tree). Base build
  `lake build +Main +Discharges +SGA3NbhdDVR +SemistableNeronBaseChangeNoSGA3 +NeronGoodModelIso +MumfordGroupLawRed`:
  OK, 14192 jobs; frozenTarget [propext, Classical.choice, Quot.sound] (VERIFIED).
- Base hash dump `hashes_0_base.txt`: 14107 constants (VERIFIED).

## Tools
- `Taint.lean` (imports TailZ48): closure of `sixContactMin_of_open41` (241711 constants); carriers = the structures
  `OpenResearchLeaves14`..`29` (16; each has `sga3_VIB_3_10`/`_Nbhd` and `mumfordGroupLaw`/`mumfordGroupLawConn`);
  tainted (type or value mentions a carrier, transitively) 519, of which 66 source declarations: the 16 research
  generations, 11 research conversions in TailZ25–46, 39 copies in HomFreeFiniteAlgClosedReroute (the `_hf` chain
  `sixContactMin_of_open17_hf`..`40_hf`, `researchLeaves9_of_open14_hf`, `x6Rows_of_open14_hf`, the `_hf` research
  conversions 19←20, 20←21, 21←22, 23←24, 25←26, SGRFold's two `_hf` theorems, …) and TailZ48's
  `sixContactMin_of_open41` (the old top: not copied, replaced by the new top module). `taint_0_base.txt` (VERIFIED).
  The same carriers serve both folds (every generation carries both fields), so both copies use this one taint list.
- `gen/gen.py` (homfree-noemb's copylib with a taint-driven item list): copies the 65 declarations verbatim up to the
  renaming `X ↦ XNS`/`x ↦ x_ns` (field 1) or `XGM`/`x_gm` (field 2, both folds), applying the fold edits; asserts that
  no removed field is left in the code. `gen/top.py` writes the top module and patches Main.
- Finding (VERIFIED by compile): copylib emits each source block's top-level `open`/`set_option` context again; copying
  out of the HF reroute repeated 220 `open … MonObj` lines, and the late conversions (19←20 … 25←26) then timed out
  at `isDefEq` even at 1000000 heartbeats. Emitting each top-level context command once fixed it: the module
  compiles at default heartbeats in 51 s.

## Step 1: sga3-nbhd (`sga3_VIB_3_10_Nbhd`) as a copy reroute
- `ZInQKernel/Contrib/OneProof/NoSGA3Reroute.lean` (generated: `python3 scratch/fold33-copy/gen/gen.py
  scratch/fold33-copy/taint_0_base.txt sga3 ZInQKernel/Contrib/OneProof/NoSGA3Reroute.lean`): 65 blocks. Edit counts:
  13 `sga3_VIB_3_10` fields (gens 14–26), 3 `sga3_VIB_3_10_Nbhd` fields (27–29), 12 + 2 pass-through lines, the five
  readers once each (`semistableNeronBaseChange_noSGA3` in `researchLeaves9_of_open14_hf_ns`, `NF.sga7_IX_3_3_of_SH'`,
  `Persists.semistablePersistsSHcp_of_SH'`, TailZ44's conversion line deleted, `Pre.sga7_IX_3_3_SH_of_pre'`), 2
  docstrings. No hNBC threading is needed: the copy imports SemistableNeronBaseChangeNoSGA3 directly.
- `ZInQKernel/OneProof/H/TailZ49.lean` (top.py sga3): `OpenResearchLeaves30` (24 fields = OpenResearchLeaves29 without
  `sga3_VIB_3_10_Nbhd`), `openResearchLeaves29NS_of_OpenResearchLeaves30`, `sixContactMin_of_open42 (r :
  OpenResearchLeaves30) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves20) := sixContactMin_of_open40_hf_ns …`.
  Main: import TailZ49, binder `OpenResearchLeaves30`, `sixContactMin_of_open42 r t l`; docstring paragraph.
- Checks (VERIFIED):
  - `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +…NoSGA3Reroute +…TailZ49`: OK, 14186 jobs
    (`build_1_sga3-tail.txt`).
  - `#print axioms ZInQ.OneProof.frozenTarget` and `HDec.HSyn.sixContactMin_of_open42`: [propext, Classical.choice, Quot.sound].
  - Closure (`closure_1_sga3.txt`, 270696 constants): none of `CToPrinted.SGA3_VIB_3_10`, `SGA3IdComp.SGA3_VIB_3_10_Nbhd`,
    `sga3_VIB_3_10_of_nbhd`, `idComp_baseChange`, `semistableNeronBaseChange_of_printed_full`; no HomFree, no sorryAx;
    the originals `OpenResearchLeaves14`, `OpenResearchLeaves29`, `sixContactMin_of_open41` are out of it,
    `OpenResearchLeaves29NS` and `sixContactMin_of_open42` in it. Bundle `OpenResearchLeaves30`: 24 fields.
  - Hash guard (`hashes_0_base.txt` → `hashes_1_sga3.txt`, `hashdiff_1_sga3.txt`): before 14107, after 14139; only
    before 0; only after 32 (TailZ49: `OpenResearchLeaves30` with its 24 projections and constructor family,
    `openResearchLeaves29NS_of_OpenResearchLeaves30`, `sixContactMin_of_open42`); changed 1: `ZInQ.OneProof.frozenTarget`.
  - `lake env lean scripts/one_proof/OpenStatements.lean`: 40 open hypotheses (41 before).
  - kinds.tsv row `sga3_VIB_3_10_Nbhd` dropped (no claims row). `render_open.py` then `--check`: ok, 40 open
    hypotheses, all classified; **32 H hypotheses, strictest 12/20, 8 others** (33, 13/20 before).
  - `frontier_crosswalk.py` then `--check`: ok (232 IDs, 31 matched).
  - `scratch/contrib-kit/DischargesTest.lean` rerun into `DischargesTest-output.txt`.
  - `uvx --offline … autoform check blueprint --lean-root .`: runs on this host; "OK: 781 articles, 2343
    dependencies, 705 fully proved, 2531 declaration name(s) resolved" (`autoform_1_sga3.txt`).

## Step 1b: the copy module moved to `ZInQKernel/OneProof/H/NoSGA3Copy.lean`
- Reason (VERIFIED, DischargesTest output): `#discharges` checks every theorem of `ZInQKernel.Contrib.OneProof.*`, and
  the projections of the copied Prop structures are theorems whose conclusion is an open field
  (`OpenResearchLeaves14NS.bostLowerBound : OpenResearchLeaves14NS → BostLowerBound`). With the copies under
  Contrib/OneProof the output grew from 48 to 301 `DISCHARGES` lines (542 with field 2's copy), almost all of them
  misleading entries in CONTRIBUTING.md's worked example. Under `ZInQKernel/OneProof/H/` (allowed for new modules by the
  task) they are not scanned, like the TailZ modules. The module's content is unchanged (`git mv`); TailZ49's import
  line, its docstring, Main's docstring and top.py changed (no declaration changed).
- Checks (VERIFIED): `lake build +Main +Discharges +…H.NoSGA3Copy +…H.TailZ49`: OK, 14186 jobs (`build_1b_move-tail.txt`);
  frozenTarget and `sixContactMin_of_open42` standard axioms; closure output identical to step 1 apart from the size
  line (`closure_1b_move.txt`); hash guard `hashes_0_base.txt` → `hashes_1b_move.txt`: before 14107, after 14705, only
  before 0, only after 598 (566 in NoSGA3Copy, now inside the dump's scope, and TailZ49's 32), changed 1
  (`ZInQ.OneProof.frozenTarget`); OpenStatements 40; DischargesTest rerun: 48 `DISCHARGES` lines as on the base, only
  the bundle name 29 → 30 changes; render_open then `--check`: ok, **32 H, strictest 12/20, 8 others**;
  frontier_crosswalk `--check` ok; autoform check OK (`autoform_1b_move.txt`).

## Step 2: goodmodel-iso (fold G) as a copy reroute
- `ZInQKernel/OneProof/H/GoodModelIsoCopy.lean` (generated: `python3 scratch/fold33-copy/gen/gen.py
  scratch/fold33-copy/taint_0_base.txt sga3,gm ZInQKernel/OneProof/H/GoodModelIsoCopy.lean`): the same 65 declarations,
  copied from the originals with both folds (suffix GM/_gm). Fold G's edit counts equal fold33-combine's gm_fold.py:
  14 `mumfordGroupLaw` fields narrowed to `GroupLaw.MumfordGroupLawDVR` (gens 14–27), 3 `qmFamilyGroupLaw_of_groupLaw` →
  `qmFamilyGroupLaw_of_dvr`, 1 `y3Connected_of_leaves` → `y3Connected_of_ab_gl ∘ qmFamilyGroupLaw_of_dvr`, 2 field swaps
  `mumfordGroupLawConn` → `neronSchemeExtensionDedekind` (gens 28, 29), 1 supplier
  `mumfordGroupLaw := GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`, 1 pass-through;
  sga3 edits as in step 1. The copy is taken from the originals rather than from NoSGA3Copy (same carriers, same 65
  declarations; names do not stack). NoSGA3Copy and TailZ49 stay, unchanged, outside frozenTarget's closure.
- `ZInQKernel/OneProof/H/TailZ50.lean` (top.py gm): `OpenResearchLeaves31` (24 fields: OpenResearchLeaves30 with
  `mumfordGroupLawConn` → `neronSchemeExtensionDedekind`), `openResearchLeaves29GM_of_OpenResearchLeaves31`,
  `OpenTextbookLeaves16` (OpenTextbookLeaves15 without `neronSchemeExtensionExists`),
  `openTextbookLeaves15_of_OpenTextbookLeaves16 (n) (h : NeronSchemeExtensionDedekind)` (supplier
  `GroupLawNeron.neronSchemeExtensionExists_of_dedekind h`), `sixContactMin_of_open43 (r : OpenResearchLeaves31)
  (t : OpenTextbookLeaves16) (l : OpenAddedLeaves20) := sixContactMin_of_open40_hf_gm …`. Main: import TailZ50, binders
  31/16, `sixContactMin_of_open43 r t l`; docstring paragraph. TailZ49's module docstring: path typo fixed (no
  declaration change).
- kinds.tsv: rows `mumfordGroupLawConn` (research) and `neronSchemeExtensionExists` (textbook) dropped; row
  `neronSchemeExtensionDedekind` added (research, published, LEAF/LEAF, flag "locator UNVERIFIED (BLR, Neron models,
  1.4 Thm 3 with 1.2 Def 1, existence half, affine Dedekind base)", packet R2, tier T4, unverified-locator, area issue
  #85; the row of goodmodel-iso's spec as fold33-combine wrote it). claims.tsv: the two held project rows (neron-ext,
  group-law) dropped.
- Checks (VERIFIED):
  - `lake build +Main +Discharges +…H.NoSGA3Copy +…H.TailZ49 +…H.GoodModelIsoCopy +…H.TailZ50`: OK, 14196 jobs
    (`build_2_gm-tail.txt`; GoodModelIsoCopy 11 s).
  - `#print axioms ZInQ.OneProof.frozenTarget` and `HDec.HSyn.sixContactMin_of_open43`: [propext, Classical.choice, Quot.sound].
  - Closure (`closure_2_gm.txt`, 270833 constants): none of the SGA 3 VI_B 3.10 names, none of
    `MumfordConn.MumfordGroupLawConn`, `mumfordGroupLaw_of_conn`, `MumfordRigidity.MumfordGroupLaw`,
    `qmFamilyGroupLaw_of_groupLaw`; no HomFree, no sorryAx; originals and the NS copies out of it, `OpenResearchLeaves29GM`
    and `sixContactMin_of_open43` in it; `NeronSchemeExtensionDedekind`, `mumfordGroupLawDVR_of_dedekind`,
    `neronSchemeExtensionExists_of_dedekind` in it; `NeronC.NeronSchemeExtensionExists` stays as a proved intermediate
    statement, no bundle field has it as type. Bundles: OpenResearchLeaves31 24 fields, OpenTextbookLeaves16 3,
    OpenAddedLeaves20 4.
  - Hash guard (`hashes_1b_move.txt` → `hashes_2_gm.txt`, `hashdiff_2_gm.txt`): before 14705, after 15313, only before 0,
    only after 608 (566 GoodModelIsoCopy, 42 TailZ50), changed 1 (`ZInQ.OneProof.frozenTarget`). Against the base
    (`hashes_0_base.txt`): only before 0, only after 1206, changed 1 (frozenTarget).
  - OpenStatements: 39 open hypotheses.
  - render_open then `--check`: ok, 39 open hypotheses, all classified; **31 H hypotheses, strictest 11/20, 8 others**.
  - frontier_crosswalk then `--check`: ok (232 IDs, 30 matched; `neronSchemeExtensionDedekind` has no frontier ID).
  - DischargesTest rerun: 38 `DISCHARGES` lines (48 before; the 10 dropped are the entries for the removed fields
    `mumfordGroupLawConn`, `neronSchemeExtensionExists`).
  - autoform check blueprint: OK, 781 articles, 2531 declaration names resolved (`autoform_2_gm.txt`); the pages naming
    `OpenResearchLeaves28.mumfordGroupLawConn` and `OpenResearchLeaves28.sga3_VIB_3_10_Nbhd` still resolve, since the
    originals stay.

Counts (render_open): base 33 H, strictest 13/20 → step 1: 32, 12/20 → step 2: 31, 11/20 (8 others throughout;
open hypotheses 41 → 40 → 39).

## Step 3: merge origin/wip/leaf-fold33b (4da8d4f3: hQ and hP23 proved outright, hand folds of Main)
- The base branch moved during the task; merged so that wip/leaf-fold33b fast-forwards to wip/fold33-copy. Main.lean
  auto-merged (binders `OpenResearchLeaves31`, `OpenTextbookLeaves16`, `sixContactMin_of_open43 r t l`; hQ, hP23
  gone, supplied by `Gamma0QExp.gamma0QExpansion_proof`, `HP23Proof.tyzProp23Printed`); the generated files
  (STATUS.md, OPEN.md, CONTRIBUTING.md, DischargesTest-output.txt) conflicted and were regenerated.
- Checks (VERIFIED): `lake build +Main +Discharges +…H.NoSGA3Copy +…H.TailZ49 +…H.GoodModelIsoCopy +…H.TailZ50`: OK,
  14208 jobs (`build_3_merge-tail.txt`); frozenTarget standard axioms; closure output identical to step 2 apart from the
  size line; hash guard `hashes_2_gm.txt` → `hashes_3_merge.txt`: 15313 → 15313, only before 0, only after 0, changed 1
  (`ZInQ.OneProof.frozenTarget`); OpenStatements 37; render_open then `--check`: ok, **31 H hypotheses, strictest
  11/20, 6 others** (37 open); frontier_crosswalk `--check` ok (29 matched); DischargesTest rerun (37 open, 38
  discharge one); autoform check OK.
- autofold dry-run on the step-2 tree (spec discharging `gagaMorphism` and `neronSchemeExtensionDedekind` by `sorry`, not
  written): parses Main/TailZ50, prints "strict count: 11/20 on 31 -> 10/19 on 29" and a TailZ51 with
  `OpenResearchLeaves32`, `OpenTextbookLeaves17`, `sixContactMin_of_open44`, which compiles (`lake env lean`, only the
  two sorry warnings) (VERIFIED).
