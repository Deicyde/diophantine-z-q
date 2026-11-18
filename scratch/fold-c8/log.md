# fold-c8 log

Base wip/leaf-fold33b b9b85486 (main + fold-b115 + fold-b116). H top `HDec.HSyn.sixContactMin_of_open79` (TailZ86,
`OpenResearchLeaves60`, `OpenTextbookLeaves18`, `OpenAddedLeaves27`). Build tree `.lake/build`, `lean/.lake/build`
reflink-copied from the fold-b116 worktree (627782cf; no Lean file differs from b9b85486).

## 1. Merges (VERIFIED, 11-17 16:10)
- `git merge origin/wip/conrad-b3` (e579047cc): clean, commit d7482351.
- `git merge 8050603b` (PR #86 head, input only): clean, commit f0294b40 (317 added files, all new; no existing file changed).
- Hygiene (commit 90e65c77): 12 scratch dry-run files that declare `HDec.HSyn` bundle generations renamed `.lean.txt`
  (c8-conrad2: C8DryRun, C8DryRunGen, C8DryRunTaint, C8FoldDryRun, gen/fold.lean; c8-conrad3: C8DryRunTaint,
  C8FoldDryRun; conrad-b3: CBDryRun; ht-abvar: HTDryRun, HTDryRunTaint, gen/top_b.lean; ht-merge: HTMergeDryRun).
  Host paths: none in the merged files. Vendored LICENSE/NOTICE files kept (CloudR2Poincare L1, L3, L4; CloudR2Hom C4SourcePort).

## 2. Base build and checks (VERIFIED, 11-17 16:38)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.C8Printed
  ZInQKernel.Contrib.OneProof.C8CFT ZInQKernel.Contrib.OneProof.ScholzeH1AbVar
  ZInQKernel.Contrib.CloudR2Poincare.FinalUnconditional`: Build completed successfully (16329 jobs; build1.txt).
  PR #86's `CloudR2Poincare/L1/Source20261116/ResidueFieldModels.lean` alone took 2123 s (35 min).
- Base hash dump (DumpCompact): 21041 constants (/tmp/fc8/hashes_fold0.txt, not committed); frozenTarget standard.
- **render_open count at base (kinds.tsv H rows): strict 5/24 on 29, strictest 5/24.**

## 3. Taint and generated fold (VERIFIED, 11-17 16:41)
- `lake env lean scratch/fold-c8/gen/Taint.lean` (c8-conrad2's taint, seeds `t09SymmIsogenyExists`, `phiAmpleIsogeny`,
  `weilPairingMumford`, `detTate`) on the base: closure 292708, 13 carriers (OpenAddedLeaves4PZ..18PZ, GaloisPieces), 71
  tainted; T/S lines: D2A6Chain 41 T + 7 S, PicZeroCharZeroCopy 26 T + 127 S, TailA 1 T + 6 S, TailZ85 1, TailZ86 1,
  Main 1 (`gen/taint_out.txt`, 2 min 17 s). No two tainted declarations share a short name.
- `python3 scratch/fold-c8/fold_c8.py --dry-run`: gen.py 69 blocks, 13 structures, readers replaced [1, 1]
  (`detTate_of_leaves4_pz l.t09SymmIsogenyExists ...` in `gluePieces_of_open4_hf_pz_eb_u`; `g12Det_of_pz m.r14det
  m.detTate ...` in `g8_g12_of_leaves3_hf_pz_eb_u` -> `C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`); excluded
  (replaced by the top section) `sixContactMin_of_open45_pz_eb_sf_u`, `_open48_eb_k954_sf_u`, `_open72_sf_u`,
  `_open73_sf_u`, `_open78`, `_open79`. Top section edited copies: `GR9.openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm`
  (consumer (iii): `hodgeTateDecompAbVar := hHT`), `openAddedLeaves18_hm`, `GR9.sixContactMin_of_open45_pz_eb_sf_u_hm`
  (consumer (ii): `openTextbookLeaves13HF_of_open16_P ... hP`), `GR9.sixContactMin_of_open72_sf_u_hm`,
  `sixContactMin_of_open79_hm`. Dry-run chain compiled first try (7.7 s, no errors), `sixContactMin_of_open79_hm`
  standard axioms.
- **Count printed by the script (autofold's rule): strict 5/24 on 29 -> 5/24 on 29; strictest 5/24 -> 5/24** (as the
  integrator expected; 3 GLUE rows out: picRepresentableAbVar, kleimanPicZeroProper954SiteQ, hodgeTateDecompOr; 3 GLUE
  rows in: conradAppB, scholzeH1AbVar, t10TateDuality; poincareComplement proved by PR #86, no row).

## 4. The fold (VERIFIED, 11-17 16:43)
- `python3 scratch/fold-c8/fold_c8.py`: wrote `ZInQKernel/OneProof/H/C8Chain.lean` and `TailZ87.lean`
  (`OpenResearchLeaves61` = 60 without hodgeTateDecompOr; `OpenAddedLeaves28` = {conradAppB, scholzeH1AbVar,
  t10TateDuality}; `openResearchLeaves60_of_OpenResearchLeaves61 n l` fills hodgeTateDecompOr by
  `DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne l.scholzeH1AbVar l.t10TateDuality`;
  `sixContactMin_of_open80 r t l` with `poincareComplement_proof` and `c8Inputs_of_leaves`), switched Main.lean,
  kinds.tsv (3 rows dropped, 3 added). claims.tsv / volatile.tsv not touched (no row for any of the six fields).
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.C8Chain
  ZInQKernel.OneProof.H.TailZ87`: Build completed successfully (16331 jobs, 30 s); frozenTarget
  [propext, Classical.choice, Quot.sound].

## 5. Checks after the fold (VERIFIED, 11-17 16:50; `run_checks.sh 1 hashes_fold0.txt`, output run_checks-fold1.txt)
- Hash guard (DumpCompact + cmp_hashes.py, cmp_fold1.txt): 21041 -> 21343, only before 0, only after 302 (C8Chain 258,
  TailZ87 44), changed only `ZInQ.OneProof.frozenTarget`. (run_checks' cmp step first failed on a stale
  `scratch/fold-b116/` path inside the copied cmp_hashes.py; fixed and rerun by hand, same files.)
- Closure (FoldCheck-fold1.txt, 296120 constants): `#print axioms ZInQ.OneProof.frozenTarget` = [propext,
  Classical.choice, Quot.sound]; absent: sorryAx, `T09Pic.PicRepresentableAbVar`, `KleimanSite.KleimanPicZeroProper954SiteQ`,
  `OpenAddedLeaves27`, `sixContactMin_of_open79`, `C8Conrad.TateTwistInvariantsInertia`, `detTate_of_leaves4_pz`,
  `GR9.sixContactMin_of_open45_pz_eb_sf_u`, `hodgeTateDecompAbVar_of_open_k954`; constants named
  `*PicRepresentable*` / `*KleimanPicZeroProper*`: 0. Present: ConradAppB, ConradPropB3Qp, ConradAppBQp,
  g12DetPZ_of_inputs, twistCharHTWt0_proof, ScholzeH1AbVar, T10_TateDuality, poincareComplement_proof,
  sixContactMin_of_open79_hm, OpenResearchLeaves61, OpenAddedLeaves28, sixContactMin_of_open80; also
  OpenResearchLeaves60 and HodgeTateDecompOr (only as the conversion's target, filled from the Scholze leaf; not
  hypotheses: `#check @frozenTarget` binders are OpenResearchLeaves61, OpenTextbookLeaves18, OpenAddedLeaves28, hPC).
  Field check: OpenResearchLeaves61 = OpenResearchLeaves60 minus hodgeTateDecompOr (27 -> 26), no type differs.
- OpenStatements: 30 open hypotheses. render_open: 29 H, strictest 5/24, 1 other; `--check` ok (4 generated files).
- DischargesTest: 23 DISCHARGES lines (no error). New lines include `OpenAddedLeaves28.scholzeH1AbVar` by
  `scholzeH1AbVar_of_old`, and `OpenResearchLeaves61.deRhamVpAbVarDirect` by
  `DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne` (from the new leaves alone; the row is LEAF/LEAF, so
  removing it would not lower the GLUE count: not done, noted for the integrator). The hodgeTateDecompOr lines left.
- frontier_crosswalk: 232 IDs, 3 matched (was 4: H-199 matched picRepresentableAbVar); `--check` ok.
- autoform check: exit 0 (776 articles, 647 fully proved).
- gate.sh: AUTOFOLD-DRYRUN-EXIT=0, TREE-UNCHANGED=yes, GATEFOLD-EXIT=0, GATEFOLD-AXIOMS=standard, **GATE=ok**.
- **render_open count after the fold: 30 open (H 29, strict 5/24, strictest 5/24, 1 other).**

## 6. AllContrib / clash check (VERIFIED, 11-17 16:55)
- The 31 Contrib modules without an olean were built first (`lake build` of them: Build completed successfully, 14652
  jobs; build-missing.txt), so every one of the 6640 Contrib modules has an olean.
- **ClashScan** (contrib-clashes' olean scan, Lean 4.35's import rule; `scratch/fold-c8/ClashScan.lean` over
  `contrib-modules.txt` = every `ZInQKernel/Contrib/*.lean` except AllContrib, plus OneProof.Main and TailZ87):
  19043 modules read, 0 missing oleans, 856345 constants; **7 fatal clashes, all pre-existing and none involving a
  module of this branch** (clashscan-fatal.txt): 6 `HDecomp.Textbook.Different` / `Contrib.Different.Local`
  (`PkgI6.TraceContainsRamificationIdx`, `PkgI6.MonogenicDVR`, `TDifferent.phiExpl/resHom/phiF/filtR`; fixed on
  wip/contrib-clashes, not on this base) and 1 `WeierstrassCurve.Affine.divisorSum`
  (`CloudB2X0Transitive.Vendor.AnthropicFLT...Def_WeierstrassCurve_GenusOnePic0` def / `TauCeti...Divisor.Sum`
  axiom). 1741 accepted duplicates; the 20 involving PR #86 / new modules (clashscan-new-modules.txt) are realized
  `eq_1` / `congr_simp` lemmas; **against CloudB3W17bReduced: one accepted duplicate
  (`TopCat.Presheaf.stalkCongr.eq_1`, both vendor Stacks `Perfect.BaseChangeStalk`), no fatal clash**.
- **Real co-import** (`lake env lean`, one process at a time):
  * base `AllContrib.lean` list alone (AllContribBase.lean): exit 0.
  * A: base list + every new CloudR2* module (PR #86, 317 files' modules): exit 0.
  * **B: base list + PR #86 + all 26 CloudB3W17bReduced modules: exit 0.**
  * C: base list + the new C8 / Scholze / de Rham modules: exit 1, `divisorSum` clash (CloudB2X0Transitive vs TauCeti).
    Pre-existing: base list + `OneProof.H.TailZ86` (the unchanged base chain) and base list + `PicZeroCharZeroCopy`
    fail with the same error. The C8 modules import the chain (C8Conrad imports PicZeroCharZeroCopy), so they inherit it.
  * AllContribC8.lean (base list + all new modules + CloudB3W17bReduced) therefore fails at the same pre-existing clash.
- AllContrib.lean is not edited (not in this task's write list; the C8 modules cannot join it until the
  divisorSum and Different clashes are fixed, e.g. by wip/contrib-clashes).
