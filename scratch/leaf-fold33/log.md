# leaf-fold33 log

Base: fork main after w82 (leaf-fold32b 03f2467d + STATUS.md wording, 5e235a40).

1. Merged wip/poincare-proof (5795bbc0) and wip/neron-sh-proof (3842078a).
2. One autofold (`scratch/leaf-fold33/autofold.json`), TailZ46, `sixContactMin_of_open39`:
   - `poincareComplement` by `PoincareComplement.poincareComplement_of_open`. Its spec in poincare-proof was written
     on 0caafe66; on this base `phiAmpleIsogeny` is supplied by `PicFix.phiAmpleIsogeny_of_printed` from the added
     leaves `mumfordKLFiniteSectionAC` and `mumfordPhiSurjectiveAC`, and `milneIsogenyQuasiInverse`, `cartierSmooth`
     are proved (`milneIsogenyQuasiInverse_proof`, `cartierSmooth_proof`), so those are used directly.
   - `blr_7_2_1` (dict-models' printed form, which replaced `neronBaseChangeStrictHenselization` in leaf-fold32) by
     `NeronSH.neronBaseChangeUnramifiedDVR_proof`: `DictModels.NeronBLR72.BLR_7_2_1` is by definition
     `ReductGlue.NeronBaseChangeUnramifiedDVR`, which neron-sh-proof proves with no hypotheses.
   - autofold: strict 16/21 on 37 -> 15/20 on 35; strictest 16/21 -> 15/20 (blr_7_2_1 was flagged "pending reading",
     so it counted GLUE: the strict GLUE count drops by one, and one LEAF field goes).
3. Checks (VERIFIED):
   - `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` and both contributions: OK.
   - `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound].
   - Hash guard (DumpCompact before/after): before 14038, after 14083, only before 0, only after 45 (all in TailZ46),
     changed 1 (`ZInQ.OneProof.frozenTarget`).
   - `lake env lean scripts/one_proof/OpenStatements.lean`: 43 open hypotheses.
   - `render_open.py` then `render_open.py --check`: ok, 43 open hypotheses, all classified (35 H, strictest 15/20, 8 others).
   - `frontier_crosswalk.py` regenerated (H-72 poincareComplement unmatched now), `--check` ok.
   - `scratch/contrib-kit/DischargesTest.lean` rerun after the fold (output saved).
4. Branch: pushed as wip/leaf-fold33b, because wip/leaf-fold33 already existed on the fork (a parallel, unfinished
   fold made before this one: the same two discharges plus pic-smooth's picZeroAbVar, autofold count
   16/21 on 37 -> 18/20 on 38, with no regeneration of the docs). pic-smooth's part is left out here: it replaces the
   GLUE field picZeroAbVar by four leaves, one of them pending reading (picZeroSmoothPosChar, GLUE), so it neither
   removes a field nor lowers the strict GLUE count (this fold: 15/20 on 35; with pic-smooth: 18/20 on 38).
5. Route A's C_d chain (gzopt-dict, a backlog task that met its target): merged wip/gzopt-dict (period-odd, cd-optimal,
   gz-optimal, heegner-32, gz-conj and gz-weil's final files; clean merge). Hand fold of Main.lean, as
   scratch/gzopt-dict/MainEdit.lean shows (rewritten for the current Main): the binder `hL3 : GZDecomp.GrossZagierHeegner`
   (kinds: composite, GLUE) is replaced by `hGZ : GZAlg.GrossZagierAlgOptCd`, `hQ : GZAlg.Gamma0QExpansion`,
   `hW : CdOpt.EtaW32Character` (published, LEAF; rows from scratch/gzopt-dict/autofold-formula.json, packet, label,
   tier and area issue of hL3), through
   `GZStatements.frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`,
   `fhNonvanishingCd_of_fhNonvanishing`, `Heegner32.grossZagierHeegnerCd_of_printed hCM`,
   `GZAlg.grossZagierFormulaCd_of_alg` and `GZConj.grossConjugationCd`; `HeckeThetaNewform` is no longer needed.
   The claims row of hL3 is removed. Strict GLUE count over all hypotheses: -1 (the 10 TYZ/GZ hypotheses: hCM, h33
   GLUE; the rest LEAF). Checks (VERIFIED): `lake build +Main +Discharges`; frozenTarget standard axioms; hash guard
   against step 3 (14083 constants, only frozenTarget changed); OpenStatements 45; render_open --check ok (35 H,
   strictest 15/20, 10 others); crosswalk regenerated, --check ok; DischargesTest rerun. Host paths in merged logs
   replaced by worktree names.
6. Merged fork main c1e4ed1b (the blueprint's height-decomposition chapter). chain-w84 then failed CHECKLR and RENDER:
   the chapter's Lean targets `HDec.HSyn.OpenTextbookLeaves13.*` were also declared by poincare-proof's dry-run
   output `scratch/poincare-proof/FoldDryRun.lean` (written on 0caafe66, where autofold's next generation had the
   same name), so autoform found them twice. The file is renamed `FoldDryRun.lean.txt` (content unchanged).
   `autoform check blueprint --lean-root .` and `autoform render ... --require-declarations` then pass (VERIFIED).
7. phi-ample (mumfordKLFiniteSectionAC proved from picRepresentableAbVar and picZeroAbVar, no new leaf): merged
   wip/phi-ample, autofold scratch/phi-ample/autofold.json -> TailZ47, `sixContactMin_of_open40`; strict
   15/20 on 35 -> 14/20 on 34, strictest the same. Checks (VERIFIED): build +Main +Discharges; frozenTarget standard
   axioms; hash guard against step 5 (only frozenTarget changed, 12 new constants, all in TailZ47); OpenStatements 44;
   render_open --check ok (34 H, strictest 14/20, 10 others); crosswalk --check ok; DischargesTest rerun; autoform
   check blueprint --lean-root . ok. Scratch copies of HDec.HSyn bundles (phi-ample's FoldDryRun.lean,
   neron-sh-proof's FoldCheck.lean) renamed .lean.txt, as in step 6.
8. homfree-noemb (homFreeFiniteAlgClosed rerouted away, no new leaf; manual fold, scratch/homfree-noemb/FOLD.md):
   merged wip/homfree-noemb; reran `scratch/homfree-noemb/Taint.lean` on this tree and regenerated the two
   contribution files with `gen/gen.py` (patched to read the top module from Main.lean instead of TailZ45, and the
   consumers header to import TailZ47): 39 + 96 declarations, top `sixContactMin_of_open40_hf` over
   `OpenTextbookLeaves14HF`. `#discharges`/OpenStatements read bundles only from ZInQKernel.OneProof modules, so a
   hand-written `OneProof/H/TailZ48.lean` (autofold's pattern) defines `OpenTextbookLeaves15` (= OpenTextbookLeaves14
   without the field, docstrings kept), its map to `OpenTextbookLeaves14HF`, and `sixContactMin_of_open41`; Main uses
   it (autofold parses the new Main). kinds/claims rows of homFreeFiniteAlgClosed dropped. Checks (VERIFIED): build
   +Main +Discharges; frozenTarget standard axioms; hash guard against step 7 (only frozenTarget changed, 12 new
   constants, all in TailZ48); closure of frozenTarget (270264 constants) has no AVB1.HomFreeFiniteAlgClosed,
   PkgI3.HomFreeFinite, HomFreeFiniteAlgClosedNoEmb or sorryAx; OpenStatements 43; render_open --check ok (33 H,
   strictest 13/20, 10 others); crosswalk --check ok; DischargesTest rerun; autoform check and render ok after
   renaming scratch/homfree-proof/FoldDryRun.lean to .lean.txt (it redeclared OpenTextbookLeaves13).
   Note for later folds: deg-det's DegEqDetTate route reads homFreeFiniteAlgClosed in characteristic p and no longer
   fits; degpoly-proof's recommended spec does not read it.
9. hW and hfx (frozenTarget binders, both proved outright with no new leaf): merged wip/etaw32-proof
   (`EtaW32Character.etaW32Character_proof`, from Mathlib's eta S/T laws) and wip/hfx-proof
   (`HfxProof.tyzTestVectorExists`; brings fork PR #39's Hurwitz approximation), hand fold of Main.lean (binders
   removed, proofs passed), kinds rows of hW and hfx and the claims row of hfx dropped. Checks (VERIFIED): build
   +Main +Discharges; frozenTarget standard axioms; hash guard against step 8 (only frozenTarget changed);
   OpenStatements 41; render_open --check ok (33 H, strictest 13/20, 8 others); crosswalk --check ok; DischargesTest
   rerun; autoform check blueprint ok.
   Not folded (log of the lead): fold33-combine's in-place prunes of sga3_VIB_3_10_Nbhd and of mumfordGroupLawConn /
   neronSchemeExtensionExists delete Lean targets named by the blueprint chapter (OpenResearchLeaves28 fields), so
   they fail autoform check; charpoly-charp needs T6 in characteristic p and conflicts with the homfree reroute.
10. hQ (frozenTarget binder, the q-expansion principle for Gamma0(N), proved outright with no new leaf): merged
    wip/gamma0-qexp (`Gamma0QExp.gamma0QExpansion_proof`), hand fold of Main.lean, kinds row dropped. Checks
    (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard against step 9 (only frozenTarget
    changed); OpenStatements 40; render_open --check ok (33 H, strictest 13/20, 7 others); crosswalk --check ok;
    DischargesTest rerun; autoform check blueprint ok. Route A's C_d chain now rests on hGZ (Gross-Zagier over the
    algebraic X0(N)) and hCM only.
11. hP23 (frozenTarget binder, TYZ Proposition 2.3 first assertion, proved outright with no new leaf): merged
    wip/hp23-proof (`HP23Proof.tyzProp23Printed`), hand fold of Main.lean, kinds row dropped. Checks (VERIFIED):
    build +Main +Discharges; frozenTarget standard axioms; hash guard against step 10 (only frozenTarget changed);
    OpenStatements 39; render_open --check ok (33 H, strictest 13/20, 6 others); crosswalk --check ok;
    DischargesTest rerun; autoform check blueprint ok.
12. sga3-nbhd and goodmodel-iso (fold G) by copy reroutes (integration task fold33-copy, fast-forwarded): copies of
    the 65 declarations of the chain that mention OpenResearchLeaves14-29 (NoSGA3Copy, GoodModelIsoCopy in
    OneProof/H), new tops TailZ49 (OpenResearchLeaves30) and TailZ50 (OpenResearchLeaves31, OpenTextbookLeaves16,
    `sixContactMin_of_open43`); no existing declaration changed, so the blueprint's targets still resolve (the earlier
    in-place attempt fold33-combine did not). sga3_VIB_3_10_Nbhd removed; mumfordGroupLawConn and
    neronSchemeExtensionExists replaced by the printed leaf neronSchemeExtensionDedekind (BLR 1.4 Thm 3 over a
    Dedekind scheme). Checks by the lead (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard
    against step 11 (only frozenTarget changed; 1206 new constants in NoSGA3Copy, GoodModelIsoCopy, TailZ49,
    TailZ50); closure of frozenTarget (271046 constants) without SGA3_VIB_3_10(_Nbhd), MumfordGroupLawConn,
    AVB1.HomFreeFiniteAlgClosed, PkgI3.HomFreeFinite, GZDecomp.GrossZagierHeegner or sorryAx; OpenStatements 37;
    render_open --check ok (31 H, strictest 11/20, 6 others); crosswalk --check ok; DischargesTest rerun; autoform
    check blueprint ok. Host paths removed from merged notes (neron-ext, fold33-copy log).
13. hCM (frozenTarget binder, consequence/GLUE) replaced by hcm-dict's printed leaf ZInQ.Contrib.HCMDict.ShimuraThm54
    (Shimura 1971 Thm 5.4 as printed over Mathlib's Weierstrass curves, short models, uniqueness dropped; "analytic
    isomorphism" is IsAnalyticUnif, characterized in Lean by isAnalyticUnif_iff): merged wip/hcm-dict, binder type
    changed (name kept), both uses take `shimuraMainCM_of_printed hCM`, kinds row from scratch/hcm-dict/kinds-row.tsv
    (published, unread, LEAF/LEAF). Strict GLUE over all hypotheses -1 (the TYZ/GZ GLUE left is h33). Checks
    (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard against step 12 (only frozenTarget
    changed); OpenStatements 37; render_open --check ok (31 H, strictest 11/20, 6 others); crosswalk --check ok;
    DischargesTest rerun; autoform check blueprint ok. The claims row of hCM (cm-primitive, done) is left as it is.
14. Review (task fold33-review, docs/research/fold33-review.md on its branch): hCM's ShimuraThm54 and
    neronSchemeExtensionDedekind are LEAF (every difference a direct instance or a step proved in Lean); the reroutes
    are clean (37 hypotheses, closure without the removed Props). hGZ: three steps between Gross-Zagier's morphism
    and the Lean pull-back on function fields are not proved in Lean (D1-D3), so under the strict rule its kinds row
    is re-flagged "pending reading" and counts GLUE (strict and strictest). With hQ and hW proved, the C_d fold is
    then count-neutral on GLUE (hL3 GLUE -> hGZ GLUE) and never raises a count. render_open --check ok.
15. phisurj and piczero-char0 (integration task fold33-pic, fast-forwarded): step 1 weilPairingMumford (GLUE) proved
    (autofold, TailZ51) and mumfordPhiSurjectiveAC rerouted (TailZ52 enters sixContactMin_of_open37_hf_gm with
    phiAmpleIsogeny := PhiSurj.phiAmpleIsogeny_of_open from picRepresentableAbVar, picZeroAbVar,
    mumfordTorsionAlgClosed): 29 H, strictest 10/19, 35 open. Step 2 picZeroAbVar (GLUE, read only in characteristic
    0) replaced by its characteristic-0 form from picLocFinType, identityComponentLFT, kleimanPicZeroProper
    (published, unread; PicZeroCharZeroCopy, TailZ53, PhiSurjCharZero): 31 H, strictest 13/18, 37 open. Checks by the
    lead (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard against step 14 (only
    frozenTarget changed; 417 new constants); closure (271480 constants) without PicZeroAbVar, PicZeroSmooth,
    MumfordPhiSurjectiveAC, WeilPairingMumford, the earlier removed Props or sorryAx; OpenStatements 37;
    render_open --check ok; crosswalk --check ok; DischargesTest rerun; autoform check ok. Host paths removed from
    merged logs (phisurj, piczero-char0).
16. identityComponentLFT (idcomp-lft, proved outright in every characteristic, no new leaf): merged wip/idcomp-lft,
    autofold scratch/idcomp-lft/autofold.json -> TailZ54, `sixContactMin_of_open47`; strict 13/18 on 31 -> 12/18 on
    30. Checks (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard against step 15 (only
    frozenTarget changed, 11 new constants in TailZ54); OpenStatements 36; render_open --check ok (30 H, strictest
    12/18, 6 others); crosswalk --check ok; DischargesTest rerun; autoform check ok. scratch/idcomp-lft/FoldDryRun.lean
    renamed .lean.txt; host path removed from its log.
17. picLocFinType (piclft, proved outright in every characteristic, no new leaf): merged wip/piclft, autofold
    scratch/piclft/autofold.json -> TailZ55, `sixContactMin_of_open48`; strict 12/18 on 30 -> 11/18 on 29. Checks
    (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; hash guard against step 16 (only frozenTarget
    changed, 10 new constants in TailZ55); OpenStatements 35; render_open --check ok (29 H, strictest 11/18, 6
    others); crosswalk --check ok; DischargesTest rerun; autoform check ok.
18. eigenformCoeffFieldFinite (composite, GLUE) proved by coeff-rational (wip/coeff-rational e85590b8, taken over
    coeff-field: same field, its diamond leaf replaced by the T_p leaf) from two printed-form leaves
    gamma1IntegralSpan (Shimura 1971 Thm 3.52) and heckePrimeIntegralToRational (T_p part of the Hecke stability of
    S_k(Gamma_1(N), Z)), both "unread: new printed leaf", locators UNVERIFIED: merged wip/coeff-rational, autofold
    scratch/coeff-rational/autofold.json -> TailZ56, `sixContactMin_of_open49`; strict 11/18 on 29 -> 13/17 on 30
    (GLUE -1, +1 hypothesis). Checks (VERIFIED): build +Main +Discharges; frozenTarget standard axioms;
    check_target.py; only Main.lean changed among existing OneProof modules (TailZ56 new); OpenStatements 36;
    render_open --check ok (30 H, strictest 13/17, 6 others); crosswalk --check ok; DischargesTest rerun; autoform
    check ok. scratch FoldCheck.lean of coeff-rational and coeff-field renamed .lean.txt (they redeclare bundles).
19. r17 (consequence, GLUE) replaced by r17-print's printed-form leaf carayolThmA (Carayol 1986 Theoreme (A), F = Q,
    weight 2, packaged form, over printed newforms; dictionary steps proved): merged wip/r17-print 785e3f29, autofold
    scratch/leaf-fold33/autofold-r17.json (r17-print's spec with eigenformCoeffFieldFinite, removed in step 18, taken
    from CoeffRational.eigenformCoeffFieldFinite_of_heckePrime) -> TailZ57, `sixContactMin_of_open50`. Per the
    integrator's rule for printed-form restatements, carayolThmA is flagged "pending review" and counts GLUE (strict
    and strictest) until a reviewer rates it: 13/17 on 30 -> 13/17 on 30 (count-neutral; another session's
    wip/leaf-fold34r folds the same result with the row LEAF, on c0f3d085 without step 18). Checks (VERIFIED):
    build +Main +Discharges; frozenTarget standard axioms; check_target.py; only Main.lean changed among existing
    OneProof modules; OpenStatements 36; DischargesTest rerun; render_open --check ok (30 H, strictest 13/17, 6
    others); crosswalk --check ok; autoform check ok. AutofoldDryRun.lean renamed .lean.txt.
20. deRhamH1AbVarT (consequence, GLUE) replaced by derham-print's two printed-form leaves deRhamVpAbVarPrinted
    (Fontaine: V_p(A) de Rham with the printed D_dR, as in Berger 2004 I.3) and bdRInvariantsPrinted (B_dR^{G_K} = K,
    dimension form), with mumfordTorsionAlgClosed; t = log[eps] and B_dR = B_dR^+[1/t] proved in Lean
    (DeRhamPrintTDict): merged wip/derham-print ccb19bd3, autofold scratch/leaf-fold33/autofold-derham.json
    (derham-print's spec, flags "pending review") with --allow-rise -> TailZ58, `sixContactMin_of_open51`. Both rows
    count GLUE until a reviewer rates them (integrator's rule), so H 13/17 on 30 -> 13/18 on 31 (GLUE +1 until the
    review; -1 against the base if both are rated LEAF). Checks (VERIFIED): build +Main +Discharges; frozenTarget
    standard axioms; check_target.py; only Main.lean changed among existing OneProof modules; OpenStatements 37;
    DischargesTest rerun; render_open --check ok (31 H, strictest 13/18, 6 others); crosswalk --check ok; autoform
    check ok. FoldDryRun.lean renamed .lean.txt.
21. gonzalezRotgerX6Ab (composite, GLUE) and elkiesX6StarFunctionField (consequence, GLUE) replaced by grx6ab-print's
    and elkies-print's printed-form leaves gonzalezRotgerThm512X6 (GR 2006 Thm 5.12, gr-dict's statement),
    x6CoarseModuli (X0(6,1) coarse moduli, reading risk on the Atkin-Lehner clause) and elkiesX6StarEvery (Elkies 1998
    section 3 for every witness), with shimuraMainThmIDeligneY3AbU, gagaMorphism, mumfordTorsionAlgClosed: merged
    wip/grx6ab-print b047ce25 (it contains wip/elkies-print 168bbb39 and gr-dict), autofold
    scratch/leaf-fold33/autofold-grx6ab-elkies.json (grx6ab-print's autofold-combined.json, flags "pending review")
    with --allow-rise -> TailZ59, `sixContactMin_of_open52`. The three rows count GLUE until reviewed: H 13/18 on 31
    -> 13/19 on 32 (GLUE +1 until the review; -2 against the base if all three are rated LEAF). Checks (VERIFIED):
    build +Main +Discharges; frozenTarget standard axioms; check_target.py; only Main.lean changed among existing
    OneProof modules; OpenStatements 38; DischargesTest rerun; render_open --check ok (32 H, strictest 13/19, 6
    others); crosswalk --check ok; autoform check ok. Scratch files that redeclare bundles renamed .lean.txt
    (grx6ab-print FoldCheck, FoldCheckCombined; elkies-print FoldDryRun; gr-dict BypassFold, BypassReach,
    FoldCheck); host paths removed from scratch/grx6ab-print/build1.txt.
22. hodgeTateDecompAbVar (consequence, GLUE) proved by hodgetate-from-dr from one new printed-form leaf
    hodgeTateDecompExists (Fontaine 1982 with both exponents unnamed), adapted by the integration task fold34-ht to the
    characteristic-0 T9 data of this tree (HodgeTatePairing{Weil0,Core0,CharZero}: hodgeTateDecompAbVar_of_open from
    hodgeTateDecompExists, mumfordTorsionAlgClosed, picRepresentableAbVar, kleimanPicZeroProper): merged wip/fold34-ht
    up to its Contrib commits (316c8da2, without its fold commit), autofold scratch/fold34-ht/autofold.json -> TailZ60,
    `sixContactMin_of_open53`; H 13/19 on 32 -> 14/18 on 32 (GLUE -1; the leaf rated as the task reports it,
    "unread: new printed leaf", LEAF). Checks (VERIFIED): build +Main +Discharges; frozenTarget standard axioms;
    check_target.py; only Main.lean changed among existing OneProof modules; OpenStatements 38; DischargesTest rerun;
    render_open --check ok (32 H, strictest 14/18, 6 others); crosswalk --check ok; autoform check ok.
    AutofoldDry.lean renamed .lean.txt.
23. bostLowerBound and gaudronRemondThm14 (consequence, GLUE) replaced by height-fix's printed-form leaves
    bostLowerBoundPrinted and gaudronRemondThm14Printed over the printed stable height, with height-fix's glue
    SemiAbelianDescendsPerfect proved by semiab-descend from the new leaf chevalleyPerfect (Chevalley over perfect
    fields), integrated by fold34-semiab: merged wip/fold34-semiab up to its Contrib and spec commit (0eca20f0, which
    merges wip/height-fix 49e6d97d and wip/semiab-descend 6a6de248, hygiene included), autofold
    scratch/fold34-semiab/autofold.json -> TailZ61, `sixContactMin_of_open54`; H 14/18 on 32 -> 17/16 on 33 (GLUE -2,
    +1 field; the three leaves rated as the tasks report them, "unread: new printed leaf", LEAF). Checks (VERIFIED):
    build +Main +Discharges; frozenTarget standard axioms; check_target.py; only Main.lean changed among existing
    OneProof modules; OpenStatements 39; DischargesTest rerun; render_open --check ok (33 H, strictest 17/16, 6
    others); crosswalk --check ok; autoform check ok.
24. javanpeykarBound (consequence, GLUE) replaced by javanpeykar-rebase's leaves over height-fix's printed stable
    height: javanpeykarPrintedMapHF (Javanpeykar 2014 Thm 1.1.1 at X0 x_K Qbar; kind consequence, pending reading) and
    constantFieldExtensionUnramifiedFinite (Stichtenoth 3.6.3(a), finite K'/K), with mumfordTorsionAlgClosed and
    height-fix's glue, now proved (step 23): merged wip/javanpeykar-rebase 4cb6a008, autofold
    scratch/leaf-fold33/autofold-javanpeykar.json (the task's spec with semiAbelianDescendsPerfect taken from
    SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley {n}.chevalleyPerfect; flags "pending review") -> TailZ62,
    `sixContactMin_of_open55`. Both rows count GLUE until reviewed: H 17/16 on 33 -> 17/17 on 34 (GLUE +1 until the
    review). Checks (VERIFIED): build +Main +Discharges; frozenTarget standard axioms; check_target.py; only Main.lean
    changed among existing OneProof modules; OpenStatements 40; DischargesTest rerun; render_open --check ok (34 H,
    strictest 17/17, 6 others); crosswalk --check ok; autoform check ok. FoldDryRun{,HF}.lean renamed .lean.txt.
25. lcal-one (Addendum 2 item 4): h11 (TYZThm11Integral) and hL29 (TYZLemma29PrintedNe3) replaced by the one printed
    leaf h21C (TYZGenusFold.TYZThm21PairsC, TYZ Thm 2.1 for pairs, tyz-genus variant B), with TYZLcalOne proved by
    lcal-one; merged wip/lcal-one, manual Main fold. h21C is a new printed leaf: "pending review", GLUE until rated.
    Same step, Addendum 2 item 2 reviewer ratings in kinds.tsv: hGZ, hCM and carayolThmA kind consequence GLUE/GLUE
    (hGZ's flag has no D4 entry on this head, nothing to drop); kleimanPicZeroProper flag "pending reading" (GLUE);
    neronSchemeExtensionDedekind restated with the hypothesis `¬ IsField D` (consumers dvr_of_dedekind and
    neronSchemeExtensionExists_of_dedekind supply IsDiscreteValuationRing.not_isField and
    NumberField.RingOfIntegers.not_isField), stays LEAF/LEAF. Y3FineModuliAb and DeligneCanonicalModelY3Every are not
    in this tree (y3abu not folded): nothing to rate. Item 3: docs/research/leaf-fold33.md line 1 corrected (landed as
    c0f3d085). claims.tsv rows h11, hL29 dropped. Count: 40 open -> 39 open; H 17/17 on 34 -> 16/18 on 34
    (kleimanPicZeroProper re-rated), others 6 (GLUE h33, hGZ) -> 5 (h21C, hCM, h33, hGZ GLUE; hBFH LEAF). Strict GLUE
    over all hypotheses 19 -> 22: +2 from the reviewer ratings, +1 from h21C pending review (one field fewer).
    Checks (VERIFIED): build +Main +Discharges +TYZLcalOne (14273 jobs); frozenTarget standard axioms;
    check_target.py; among existing OneProof modules only Main.lean changed (Contrib MumfordGroupLawNeron.lean changed
    by the reviewer fix, as intended); OpenStatements 39; DischargesTest rerun; render_open --check ok (34 H,
    strictest 16/18, 5 others); crosswalk --check ok; autoform check ok.
26. gonzalezRotgerProp56X6 (consequence, GLUE) removed by eichler-bound's bypass, integrated by fold34-eichler: merged
    wip/fold34-eichler up to its Contrib commit b6645db0 (R5fpCountLeHF; merges wip/eichler-bound 09896d1f, hygiene
    included), its scratch tools from fd1377d8, then scratch/fold34-eichler/replay.sh on this head: copy
    OneProof/H/EichlerBoundCopy.lean (gen.py from the taint run of this head) + TailZ63 (OpenResearchLeaves39,
    `sixContactMin_of_open56`), Main patched, kinds row dropped (claims row already dropped by inbox 1). No new leaf:
    39 open -> 38 open; H 16/18 on 34 -> 16/17 on 33. Checks (VERIFIED): build +Main +Discharges + copy + TailZ63
    (14288 jobs); frozenTarget standard axioms; check_target.py; among existing OneProof modules only Main.lean
    changed; closure check (bundle without the field, count Props supplied by EichlerBound.r5fpCountLe_of_two);
    OpenStatements 38; DischargesTest rerun (the 5 gonzalezRotgerProp56X6 lines gone); render_open --check ok (33 H,
    strictest 16/17, 5 others); crosswalk --check ok; autoform check ok.
