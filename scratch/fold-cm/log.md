# fold-cm results log

Base: wip/leaf-fold33b 0bcb3b0b1 (top `HDec.HSyn.sixContactMin_of_open80`, TailZ87, `OpenResearchLeaves61`,
`OpenTextbookLeaves18`, `OpenAddedLeaves28`; render_open: H strict 5/24 on 29).
Ruling quoted (Jack, to "Should [the CM-branch package] fold now?"): "Fold now at +4 (Recommended)".
Build artifacts: fold-c8's .lake/build (head be73b91c5, no ZInQKernel/ difference to 0bcb3b0b1) reflink-copied.

## 1. Components (VERIFIED, git)
* origin/wip/cm-fold-rebase 664e00417, merge-base with the base 67950e829 (top open76, TailZ83). 106 files, all added
  (no existing file modified). Its route: `sixContactMin_of_open77_cm` over TailZ80's GR9 chain and cm-branch2's
  `CMBranch/R5Prune*` copies, base `CMBranch.sixContactMin_of_open4_cm`.
* origin/wip/y3-x6b 9a2bbbe3f, on top of 664e00417; 61 files, all added. Its route copies the CM route's weak-row
  copies (`_y3`).

## 2. The live chain of the base (VERIFIED, read in ZInQKernel/OneProof/H/)
open80 (TailZ87) -> open79_hm (C8Chain) -> open72_sf_u_hm -> open45_pz_eb_sf_u_hm -> open37..8 `_sf_u_c8`
-> open7/6/4 `_hf_pz_eb_u_c8` (C8Chain L775: base `sixContactMin_of_open4_hf_pz_eb_u_c8`, NoCM/FS5 at L705-708).
Three copy reroutes since the components' base: SSFChain (`_sf`, TailZ84), D2A6Chain (`_u`, TailZ85), C8Chain (`_c8`/`_hm`,
TailZ87). The live base reads `r.r6 : D2A6.R6U` (`modelG3G6_of_leaves3U`, `linkedTateLocal_of_leaves3_hf_u`,
`kernelFieldExists_of_split_hf_u''`) and `l.c8` (GaloisPiecesC8 in `afterG7_of3_hf_pz_eb_u_c8`).
The CM base `CMBranch.sixContactMin_of_open4_cm` (Open4.lean) reads `r.r6 : PkgI2.RaynaudCriterionNF` (NC readers
`modelG3G6NC_of_leaves3`, `linkedTateLocalNC_of_leaves3_hf`, `kernelFieldExistsNC_of_split_hf`), and
`l.t09SymmIsogenyExists` through `detTate_of_leaves4_pz`: fields that the u/c8 generation-4 bundles
(`OpenResearchLeaves2EBU`, `OpenAddedLeaves4PZC8`) no longer have.

## 3. Manuscript checks (VERIFIED by reading diophantine_zq.tex; computation below)
* `pullback_check.py` -> `pullback_check.txt`: G^6 - 97200 F^2 - H^2 = 0 exactly (F, G from L381-383, H from L512);
  prime support of discriminants, leading coefficients and pairwise resultants of the ten factors = {2,3,5,7,11,13};
  J(inf) = -57600/7^6 is not a branch value.

## 4. Inbox 84.1 (VERIFIED, read on this host 18:55)
The running autoland loop (started 11-17 04:14) runs the autoland script autoland-loop.sh (mtime 04:14), whose docs-only
merge filter has no claims.tsv/volatile.tsv exemption. The exemption exists only in autoland-loop.sh.new (15:23,
not installed). So 84.1 is NOT live.

## 5. Merge of component 1 and the CM base on the live bundles
* `git merge 664e00417` (5cb492e59): clean, all files added.
* `ZInQKernel/Contrib/OneProof/CMBranchUC8.lean` (new): cm-branch's localized theorems composed with d2a6b's and
  fold-c8's replacements; top `HDec.HSyn.sixContactMin_of_open4_cm_u_c8 (r : OpenResearchLeaves2EBU)
  (t : OpenTextbookLeaves4HFPZ) (l : OpenAddedLeaves4PZC8) (g : OpenGlue4) h20 hYu hθ + 7 CM inputs`.
  `lake env lean`: 0 errors (VERIFIED, second try; first try missed the `g7DegreeBound_gp4` argument).
* Dirty scan of the base top (`DirtyLive.lean` -> `dirty-live.tsv`, 6.7 min): 963 dirty of 97078 ZInQKernel constants;
  722 in D2A6Chain, 130 in C8Chain, 1 TailZ87, 0 in SSFChain; the 109 in the original tree are covered by
  cm-branch2's `_r5` copies or are the deleted GR/FS5 producers (checked by name).

## 6. Component 1 folded (VERIFIED)
Generators (scratch/fold-cm/gen/): mk_top_live.py -> OneProof/H/CMTopLive.lean (31 chain theorems open80 ... open6
`_cm`, c : CMInputs3 threaded; base `sixContactMin_of_open4_hf_pz_eb_u_c8_cm` from CMBranchUC8); DirtyCM.lean ->
dirty-cm.tsv (939 dirty of 97067); gen_r5live.py -> OneProof/H/CMR5_1, CMR5_2, CMR5 (117 new `_r5` copies, 74 reused
from cm-branch2's CMBranch/R5Prune*; the 3 cm-fold-rebase patches applied 5/1/1 times); gen_open81.py -> OneProof/H/CMOpen.lean
(60, 59, 54SFU, GR9 36EBCFSFU, 35EBCFSFU without the GR field) and TailZ88.lean (OpenResearchLeaves62,
sixContactMin_of_open81); fold_main1.py -> Main.lean + kinds.tsv (-gonzalezRotgerThm512X6RCF, +cmFibreSplit glue,
+fowlerProp27, cmjDegree, cmPotentialGood, cmHeight62 with flags beginning 'pending review').
Every generated module compiled on the first try. Merge hygiene: CMBranchMain.lean, top2_header.lean, MainDryRun.lean
renamed .lean.txt; host paths removed from cm-branch/gen/mk_localize.py, cm-branch2/gen/gen_open73.py.
Checks (run_checks-fold1.txt): build Main + Discharges + new modules EXIT 0 (16353 jobs); frozenTarget standard axioms;
hash guard 21343 -> 22561, only frozenTarget changed, 1218 new (CMR5_1 428, CMR5_2 514, CMR5 45, CMOpen 161, CMTopLive 32,
TailZ88 38); closure 295824: sorryAx, GonzalezRotgerThm512X6RCF, GonzalezRotgerThm512X6, gonzalezRotgerThm512X6_of_rcf,
r5ptProps_of_thm512, gonzalezRotgerX6Ab_of_print, R5ptProps, FS5NoCM.R1R2fpFullProps, the NoCM bases
open4_hf_pz_eb(_u_c8), OpenResearchLeaves61, open80 absent; the five CM statements, coxProperLattice_proof,
HeightAdditivityUpper, ReducedCMPeriod, open81 present. Field check: 62 = 61 - gonzalezRotgerThm512X6RCF + 5 CM fields.
OpenStatements 34; render_open: **33 H hypotheses, strict 5/28, strictest 5/28** (expected 5/28 on 33 after both; +4 vs
5/24 on 29); --check ok; crosswalk 232 IDs, 3 matched, --check ok; DischargesTest 131 DISCHARGES lines (projection noise of
the copied structures), no error; autoform check exit 0 (776 articles, 647 fully proved); gate.sh GATE=ok.
Remaining GR-named constants in the closure (48): bundle fields `gonzalezRotgerX6Ab` (filled from x6CoarseModuli) and
`gonzalezRotgerProp56X6` of the `_r5` copies (component 2's scope).

## 7. Component 2 folded (VERIFIED)
Merge 9a2bbbe3f (037839574): clean, all files added; hygiene: scratch/y3-x6b/MainDryRun.lean renamed .lean.txt; no host
path, no vendored code. Generators: gen_y3live.py (y3-x6b's gen_y3b.py imported; GR9 entries replaced by the live
`_sf_u_c8` / `_sf_u` copies; suffix `_y3c` since y3-x6b's `_y3` names exist in Contrib/OneProof/Y3X6/Copy*) ->
OneProof/H/Y3Copy1-6 (274 blocks; first compile failed on one reference to the deleted live 35->34 conversion inside
the `_cm` top chain theorems; those three (open72_sf_u_hm_cm, open79_hm_cm, open80_cm) added to DELETE; second compile
EXIT 0); gen_top_y3.py -> OneProof/H/Y3Open.lean + TailZ89.lean (OpenResearchLeaves63, sixContactMin_of_open82; standard
axioms first try; TailZ89 imports TailZ88 so no constant leaves the environment); fold_main2.py -> Main.lean + kinds.tsv
(-x6CoarseModuliIdeal, -elkiesX6StarEveryIdeal; +y3ToP1j consequence with flag beginning 'pending review', +heckeSqrtBranchAny
glue with flag beginning 'on-the-spot: the Y3-only argument ... is not in the manuscript').
Checks (run_checks-fold2.txt): build EXIT 0 (16364 jobs); frozenTarget standard; hash guard 22561 -> 24772, only
frozenTarget changed, 0 removed, 2211 new (Y3Copy1-6, Y3Open, TailZ89); closure 295296: every X6 clause def (X6Props,
R2X6Props, CMExists, X6Surj, R2X6PropsIff), X6 leaf (X6CoarseModuliIdeal, ElkiesX6StarEveryIdeal, X6CoarseModuli,
ElkiesX6StarEvery, ElkiesX6StarPrinted, ElkiesX6StarFunctionField, ElkiesEquationsX6Ab, BabaGranathRationalAb, GonzalezRotgerX6)
and producer (x6Rows_of_leavesW, gonzalezRotgerX6Ab_r5_of_coarse, x6ModuliWitness_of_coarse, elkies_coordinate), R1R2fpRepW(_r5),
R1R2fp, X6ConicModel, R5ptProps, every Gonzalez-Rotger 5.12 constant, the NoCM base, OpenResearchLeaves61/62, open80/81 absent;
Y3ToP1j, R1R2fpY3, HeckeSqrtBranchAny, CM statements present. Field check: 63 = 62 - x6CoarseModuliIdeal -
elkiesX6StarEveryIdeal + y3ToP1j + heckeSqrtBranchAny. ClosureX6.lean -> closure-x6.txt (62 name matches, each classified in
the report: 23 projections `gonzalezRotgerProp56X6`/`gonzalezRotgerCountX6(Ab)` of type GR56.R5fpCountLe, filled by the proved
`EichlerBound.r5fpCountLe_of_two`; quaternion elements `x6`, `x6i` (LeafQCheck, PeriodGlue); `X6ConicModel_y3c := True` and its
carried fields; `x6Rows_of_open14_..._y3c` (patched: builds R1R2fpY3 from y3row); GRCountX6 helpers of the proved count;
FS5NoCM auxiliary `_proof_1` terms, `FS5NoCM.CMOptimalEmbedding` (lower added bundles), `CMBranch.NoCMAt`, `ConjMapsNoCM` (proved)).
OpenStatements 34; render_open: **33 H hypotheses, strict 5/28, strictest 5/28** = the integrator's expected count;
--check ok; crosswalk 232 IDs, 3 matched, --check ok; DischargesTest 135 DISCHARGES lines, no error; autoform exit 0
(776 articles, 647 fully proved); gate.sh GATE=ok.

## 8. Final
Report docs/research/fold-cm.md (Manuscript check: no error; L411-418 Gram matrix VERIFIED by gram_check.py, L511-519
by pullback_check.py; L481-509 bypassed, unchecked). Count: 5/24 on 29 -> 5/28 on 33 (expected). Inbox 84.1: not live.
