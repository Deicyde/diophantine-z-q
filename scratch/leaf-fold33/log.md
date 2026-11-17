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
27. Inbox 3 readings (kinds.tsv: sga7_IX_3_5_ForwardGeom LEAF/LEAF; raynaudSemistableSHOr reading flags cleared;
    sga7_IX_3_3_SHpre consequence GLUE with the three-step flag; hGZ flag names D1, D2, jacobiSym = epsilon_D) and the
    SGA 7 IX locators in docstrings (144 comment-only edits: Prop. 3.3 -> Cor. 3.3, semistable reduction Def. 3.4).
    H 16/17 on 33 -> 17/16 on 33.
28. Fork PRs #54 (mumfordTorsionAlgClosed_proof, 9f54c2cc) and #55 (gagaMorphism_proof, d81efece), both verified by
    fold34-pr and by the reviewer's second compile (inbox 2, 4): merged, one autofold
    scratch/leaf-fold33/autofold-pr54-55.json (fold34-pr's two specs combined) -> TailZ64, `sixContactMin_of_open57`;
    vendored LICENSE/NOTICE kept; no new leaf. 38 open -> 36 open; H 17/16 on 33 -> 16/15 on 31. Checks (VERIFIED):
    build +Main +Discharges (16038 jobs, PR libraries included); frozenTarget standard axioms; check_target.py; only
    Main.lean changed among existing OneProof modules; closure (no sorryAx, the two fields gone from the bundles);
    OpenStatements 36; DischargesTest rerun, no error; render_open --check ok (31 H, strictest 16/15, 5 others);
    crosswalk --check ok; autoform check ok.
29. Batch for w96 (inbox 6, 7, 9 and cfext-proof), one autofold scratch/leaf-fold33/autofold-batch-w96.json -> TailZ65,
    `sixContactMin_of_open58`: merged wip/cfext-proof 3849bd80, wip/r17-rebase 4095ce12, wip/htnew-print 8f700a64,
    wip/pb-fix3 6a2187dd (hygiene: 10 scratch dry-run files renamed .lean.txt). Spec: constantFieldExtensionUnramifiedFinite
    := CFExtProof.constantFieldExtensionUnramifiedFinite_proof (outright, cfext-proof); carayolThmA (r17-print's leaf)
    := CarayolPrinted.carayolThmA_of_irr from r17-rebase's leaf carayolThmAIrr (Burnside clause proved), flagged
    "pending reading: conductor clause (DDT 1997 Thm 3.1 / Carayol 1986 0.8)" (inbox 6); eigenformHTNew := htnew-print's
    eigenformHTNew_of_printed from modularHTPrinted; r11r12 := pb-fix3's panBerger_of_printedPV from panPrintedP and
    bergerPrintedV; eigenformCoeffFieldFinite in both proof terms replaced by coeff-rational's
    eigenformCoeffFieldFinite_of_heckePrime {n}.gamma1IntegralSpan {n}.heckePrimeIntegralToRational. New printed leaves
    "pending review" (inbox 7), all four new rows GLUE/GLUE. Inbox 9: dsThm966Printed locator pp. 513-514 in kinds.tsv
    and both docstrings (DSCoeffExt.lean, DSThm966EV.lean). Count: 36 open -> 36 open; H 16/15 on 31 -> 16/15 on 31
    (cfext -1 field -1 GLUE; r11r12 one GLUE -> two GLUE; the other two GLUE for GLUE). Checks (VERIFIED): build
    +Main +Discharges (16047 jobs); frozenTarget standard axioms; check_target.py; only Main.lean changed among existing
    OneProof modules; closure (no sorryAx); OpenStatements 36; DischargesTest rerun, no error; render_open --check ok
    (31 H, strictest 16/15, 5 others); crosswalk --check ok; autoform check ok.
30. Batch for w97 (inbox 10, 11), one autofold scratch/leaf-fold33/autofold-batch-w97.json (--allow-rise: the
    integrator asked for these restatements with their new leaves pending review) -> TailZ66,
    `sixContactMin_of_open59`: merged wip/r16-det 595ac5d5 (with r16-close), wip/y3-fix 9b4af21f, wip/sga33-steps
    92449928 (hygiene: 12 scratch fold files renamed .lean.txt). r16CoreY := AfTateLam.r16CoreY_of_ds965 from heckeJ1DS,
    afShimura, afCharpolyDS965, igusaGL2DS; shimuraMainThmIDeligneY3AbU := Y3Fix.shimuraMainThmIDeligneY3AbU_of_print
    from y3FineModuliAbP, deligneCanonicalModelY3EveryH (supersedes y3abu-print; grx6ab/elkies read the old field
    through the generated conversion); sga7_IX_3_3_SHpre := SGA33Steps.shpre_of_cor33 from sga7_IX_Cor3_3 (three
    reading steps proved); {t}.mumfordTorsionAlgClosed replaced by PR #54's proof. All seven new rows pending review,
    GLUE. Count: 36 open -> 40 open; H 16/15 on 31 -> 16/19 on 35 (3 GLUE fields out, 7 pending-review leaves in; -3
    GLUE once the leaves are rated LEAF). Checks (VERIFIED): build +Main +Discharges (16058 jobs); frozenTarget standard
    axioms; check_target.py; only Main.lean changed among existing OneProof modules; closure (no sorryAx); OpenStatements
    40; DischargesTest rerun, no error; render_open --check ok (35 H, strictest 16/19, 5 others); crosswalk --check ok;
    autoform check ok.
31. Reviewer verdicts applied (inbox 13a: h21C composite GLUE; inbox 16 queue10: modularHTPrinted, panPrintedP,
    bergerPrintedV, carayolThmAIrr, bdRInvariantsPrinted, deRhamVpAbVarPrinted, elkiesX6StarEvery,
    gonzalezRotgerThm512X6, x6CoarseModuli, javanpeykarPrintedMapHF, bostLowerBoundPrinted, gaudronRemondThm14Printed
    consequence GLUE/GLUE; chevalleyPerfect, hodgeTateDecompExists pending reading GLUE; gamma1IntegralSpan LEAF/GLUE
    (strictest); heckePrimeIntegralToRational LEAF/LEAF). H strictest 16/19 -> 11/24 on 35.
32. Manual Main folds of two binders (inbox 14, 15a): hgz-steps (wip/hgz-steps 92fd272e, with gz-dict2's
    GrossZagierPlane): hGZ retyped to ZInQ.GZSch.GrossZagierCurveCd through GZSch.grossZagierAlgOptCd_of_curve
    (D1, D2, model, points, cusp proved); h33-fix (wip/h33-fix 9b70b564, with h33-dict): h33 -> h33a :
    ZInQ.H33Fix.TYZThm33Alg through H33Fix.tyzThm33_of_alg (isX0IsoAlg_eta proved). Both new rows pending review
    (GLUE), kinds rows from the tasks' kinds-row.tsv; locators.md row for GrossZagierCurveCd appended. Count unchanged
    (40 open; others: h21C, hCM, h33a, hGZ GLUE, hBFH LEAF). kleiman-section2 (inbox 15b) deferred: its hand fold
    must be regenerated on this top. Checks (VERIFIED): build +Main +Discharges (16069 jobs); frozenTarget standard
    axioms; check_target.py; OpenStatements 40; DischargesTest rerun, no error; render_open --check ok (35 H,
    strictest 11/24, 5 others); crosswalk --check ok; autoform check ok.
33. Batch for w98, one autofold scratch/leaf-fold33/autofold-batch-w98.json -> TailZ67, `sixContactMin_of_open60`:
    merged wip/bdr-inv 3633c220, wip/derham-direct 606f4565, wip/javanpeykar-direct 35d256d0 (its contribution moved
    from scratch to Contrib/OneProof/JavanpeykarDirect.lean). bdRInvariantsPrinted := BdRInv.bdRInvariantsPrinted_proof
    (outright, from the in-tree Tate twist and Ax-Sen-Tate theorems); deRhamVpAbVarPrinted :=
    DeRhamPrint.Direct.deRhamVpAbVarPrinted_of_direct from deRhamVpAbVarDirect (Berger II.5.1 p. 19 as printed; the
    queue10 step dim_K -> dim_Qp proved); javanpeykarPrintedMapHF := JavanpeykarDirect.javanpeykarPrintedMap_of_thm111
    from javanpeykarThm111 (Javanpeykar Thm 1.1.1 over its own objects; both reading steps proved). The two new leaves
    pending review (GLUE). Count: 40 open -> 39 open; H strictest 11/24 on 35 -> 11/23 on 34 (-1 field -1 GLUE; -2
    GLUE more if the reviewer rates the two new leaves LEAF). Checks (VERIFIED): build +Main +Discharges (16073 jobs);
    frozenTarget standard axioms; check_target.py; only Main.lean changed among existing OneProof modules; OpenStatements
    39; DischargesTest rerun, no error; render_open --check ok (34 H, strictest 11/23, 5 others); crosswalk --check ok;
    autoform check ok.
34. Reviewer verdicts queue11/queue12 and the sga7_IX_3_5 ruling (inbox 18, 19): afCharpolyDS965, afShimura,
    heckeJ1DS, y3FineModuliAbP, deligneCanonicalModelY3EveryH, sga7_IX_Cor3_3, sga7_IX_3_5_ForwardGeom, hGZ, h33a
    kind consequence GLUE/GLUE; TYZThm33Alg.lean docstring constant 8. Check of every row folded since c0f3d085: none
    scores LEAF without a reviewer's LEAF rating. H strictest 11/23 -> 10/24 on 34.
35. h21c-steps (inbox 20), manual Main fold: h21C -> h21S (ZInQ.Contrib.H21CSteps.TYZThm21Span, Thm 2.1 with pi^U
    through Thm 2.4(1) as span of the six f_delta; injectivity and the 8-sum equivalence proved), via
    H21CSteps.tyzThm21PairsC_of_span; kind consequence, pending review. r3-residual (inbox 23, wip/r3-residual
    73ac1620, build logs left out, scratch R3*.lean renamed .lean.txt): autofold scratch/leaf-fold33/autofold-r3.json
    -> TailZ68, `sixContactMin_of_open61`: bostLowerBoundPrinted := R3Residual.bostLowerBoundPrinted_of_an from
    bostLowerBoundAn, gaudronRemondThm14Printed := R3Residual.gaudronRemondThm14Printed_of_an from
    gaudronRemondThm14An (R3 "uniformization clauses imply biholomorphic" proved), mumfordTorsionAlgClosed by PR #54's
    proof; both new leaves kind consequence, pending review. Its third retype (javanpeykarPrintedMapHF ->
    javanpeykarAnMin) not applied: that field was already replaced by javanpeykar-direct's javanpeykarThm111 (step 33).
    Count unchanged: 39 open; H strictest 10/24 on 34; others h21S, hCM, h33a, hGZ GLUE, hBFH LEAF. Checks (VERIFIED):
    build +Main +Discharges (16077 jobs); frozenTarget standard axioms; check_target.py; OpenStatements 39;
    DischargesTest rerun, no error; render_open --check ok; crosswalk --check ok; autoform check ok.
36. fold-kleiman2 (inbox 15b, 21) replayed: merged kleiman-section2 through fold-kleiman2's merge 5bd559d8 (hygiene:
    scratch bundle files .lean.txt; KleimanPicZeroProperQuot.lean lands with the leaf), scratch/fold-kleiman2/gen/gen.py
    --write -> copy reroute TailZ69 (OpenAddedLeaves26, `sixContactMin_of_open62`, 15 declarations copied, none
    changed): kleimanPicZeroProper -> kleimanPicZeroProper954, kind consequence GLUE, flag "LN-site vs big-site fppf
    sheafification comparison not in Lean (Def. 4.1 accepts Pic_(fppf), read 11-17)"; claims row dropped.
    gamma1-basis (inbox 24, wip/gamma1-basis f7046ab6): autofold scratch/leaf-fold33/autofold-gamma1.json -> TailZ70,
    `sixContactMin_of_open63`: gamma1IntegralSpan (LEAF/GLUE strictest) := Gamma1Basis.gamma1IntegralSpan_of_basis from
    gamma1IntegralBasis (kind consequence, pending review: strict +1 GLUE until rated, then LEAF/LEAF expected).
    hcm-lattice (wip/hcm-lattice b3d51684; HCMLattice.lean moved from scratch to Contrib/OneProof; scratch copies
    .lean.txt), manual Main fold: hCM retyped to ZInQ.Contrib.HCMLattice.ShimuraThm54Local through
    HCMLattice.shimuraMainCM_of_local (IsAnalyticIso, Weierstrass-map step by Liouville, sInvLat p-components and the
    local-global principle proved); kind consequence, pending review. Count: 39 open; H strict 10/24 (strictest 10/24)
    on 34; others h21S, hCM, h33a, hGZ GLUE, hBFH LEAF. Checks (VERIFIED): build +Main +Discharges (16082 jobs);
    frozenTarget standard axioms; check_target.py; only Main.lean modified among existing OneProof modules;
    OpenStatements 39; DischargesTest rerun, no error; render_open --check ok; crosswalk --check ok; autoform check ok.
37. Batch for w99 (inbox 25-27): merged wip/htdecomp-or eba82cb7, wip/hecke-pin d08347d3 (proofs only: the fold's leaf
    set is unchanged), wip/x6-coarse 0dc0c1fa, wip/h33-d1 4b12a442 with eps-splitting (build logs left out; scratch
    dry-run files .lean.txt). Autofold scratch/leaf-fold33/autofold-batch-w99.json -> TailZ71, `sixContactMin_of_open64`:
    hodgeTateDecompExists := HodgeTateOr.hodgeTateDecompExists_of_or from hodgeTateDecompOr (C_p-dualization proved);
    x6CoarseModuli := X6ALIdeal.x6CoarseModuli_of_ideal from x6CoarseModuliIdeal; elkiesX6StarEvery :=
    X6ALIdeal.elkiesX6StarEvery_of_ideal' from elkiesX6StarEveryIdeal (shimuraMainThmIDeligneY3AbU through y3-fix's
    proof, mumfordTorsionAlgClosed by PR #54's). Manual Main fold (h33-d1): h33a -> h33c (H33D1.TYZThm33CurveSome),
    hGZ -> hGZss (GZSplitUnique.GrossZagierCurveCdSplitSome; model uniqueness and eps_D splitting proved). All new rows
    consequence, pending review (h33c keeps the G5/G2 strong-approximation flag). Inbox 26: h21S flag (clause 1 on the
    corrected symmetric reading; variant B Lean-proved), modularHTPrinted locator Gee 2022 Fact 4.20 (4.19, p. 28).
    Count: 39 open; H 10/24 on 34; others h21S, hCM, h33c, hGZss GLUE, hBFH LEAF. Checks (VERIFIED): build +Main
    +Discharges (16093 jobs); frozenTarget standard axioms; check_target.py; only Main.lean modified among existing
    OneProof modules; OpenStatements 39; DischargesTest rerun, no error; render_open --check ok; crosswalk --check ok;
    autoform check ok.
38. Jack's ruling (inbox 31): a row counts LEAF only after a reader has checked it against the printed page.
    render_open.py: UNREAD_MARKERS ("unread", "UNVERIFIED", "recalled", "one model review", "pending reading",
    "pending review") and must_be_glue(flag); kinds_row_problems flags a LEAF row with such a flag; autofold.py scores
    new leaves with must_be_glue; unit test scripts/one_proof/test_scoring.py (a published row flagged "unread: ..."
    scores GLUE); OPEN.md Kernel-wide readings line. kinds.tsv: dsThm965Printed, heckePrimeIntegralToRational,
    neronSchemeExtensionDedekind, picRepresentableAbVar, hBFH LEAF -> GLUE. Counts before: H strict/strictest 9/25 on
    34, all hypotheses 10/29 on 39; after: H 5/29 on 34, all 5/34 on 39. Inbox 28 re-kinds: h21S, igusaGL2DS,
    javanpeykarThm111, bostLowerBoundAn, gaudronRemondThm14An consequence; deRhamVpAbVarDirect pending reading;
    gamma1IntegralBasis published with the reviewer's flag (GLUE under the ruling). Inbox 29c: r3-residual.md count
    corrected (count-neutral after review).
39. After Jack's ruling of 11-17 (inbox 42: no more Gross-Zagier or TYZ work; nothing under frozenTarget's TYZ/GZ
    arguments is folded from here on), H rows only, one autofold scratch/leaf-fold33/autofold-batch-w103.json ->
    TailZ72, `sixContactMin_of_open65`: merged wip/gr512-bridge e055e0fa, wip/htnew-assembly b7696d21,
    wip/kleiman-site 7e35ad6c, wip/ga-rigidity f9e83fdb, wip/pb-pst cad410ec, wip/y3-hodge 90731d3d (build logs left
    out; dry-run scratch files .lean.txt). gonzalezRotgerThm512X6 <- gonzalezRotgerThm512X6RCF (GR 2006 Thm 5.12 over
    the ring class field; cited print); modularHTPrinted <- modularHTCoeff (cited print, Gee 2022 Fact 4.20);
    kleimanPicZeroProper954 <- kleimanPicZeroProper954SiteQ (Kleiman 9.5.4, LN-site vs big-site fppf comparison
    proved; cited print); sga7_IX_Cor3_3 and sga7_IX_3_5_ForwardGeom <- their Def34 forms (G_a rigidity proved; SGA 7
    IX read 11-17; cited print); bergerPrintedV <- bergerPrintedVT (Berger 2002 Thm 0.7, V1/V2/P2 cleared; cited
    print); deligneCanonicalModelY3EveryH <- deligneCanonicalModelY3EveryPrint (Deligne / Shimura as printed; cited
    print). Every new row kind consequence, pending review (GLUE until rated). None is on-the-spot. Reviews rows of
    the replaced fields moved to reviews-retired.tsv. gr-isogdeg not folded: its target gaudronRemondThm14Printed was
    replaced by gaudronRemondThm14An (r3-residual, step 35). Count: 39 open; H 5/29 on 34 (unchanged; up to -7 GLUE as
    the reviewer rates the new rows). Checks (VERIFIED): build +Main +Discharges (16102 jobs); frozenTarget standard
    axioms; check_target.py; only Main.lean modified among existing OneProof modules; OpenStatements 39;
    DischargesTest rerun, no error; render_open --check ok; crosswalk --check ok; autoform check ok; test_scoring ok.
40. Batch for w104 (inbox 43, 44), one autofold scratch/leaf-fold33/autofold-batch-w104.json -> TailZ73,
    `sixContactMin_of_open66`: merged wip/charpoly-p 9df59d44, wip/charpoly-port 67aaa436 (59 vendored Anthropic FLT
    modules under CharPolyPort/Vendor/, Apache-2.0 notices kept), wip/igusa-gal 48b5c4e5, wip/derham-range f3832ec7
    (dry-run scratch files .lean.txt). charPolyIndepOfEllAlgClosed := CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'
    DegPolyFLT.degHomogPoly (Mumford 19 Thm 4 proved outright in every characteristic, no new leaf: -1 field);
    igusaGL2DS := X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome from igusaGL2DSGalSome (DS Thm 7.6.3 printed form; cited
    print, not in diophantine_zq.tex; consequence, pending review until the reviewer rates it). derham-range: Lean only
    (DeRhamRange.lean: range_iotaF_eq_bdrFix, deRhamVpAbVarDirect_iff_adm); the deRhamVpAbVarDirect row keeps the
    leaf with derham-range's pending-reading flag (GLUE). None on-the-spot. Count: 39 -> 38 open; H strict 5/29 on 34
    -> 4/29 on 33. Checks (VERIFIED): build +Main +Discharges (16177 jobs); frozenTarget standard axioms;
    check_target.py; only Main.lean modified among existing OneProof modules; OpenStatements 38; DischargesTest rerun,
    no error; render_open --check ok; crosswalk --check ok; autoform check ok.
41. Main 19fdd483 carries the integrator's coeff-field-tc fold, written as main's TailZ66 (on main's TailZ65), which
    clashes with this branch's TailZ66..73. Merged origin/main (merge commit): this branch's TailZ66 and Main kept,
    main's TailZ66 superseded, generated docs ours + regenerated, STATUS.md theirs + render; the coeff-field-tc proof
    files (EigenformCoeffFieldFiniteProof.lean, vendored Tau Ceti files, ThirdParty/TauCeti/NOTICE) come in with the
    merge. Then the fold redone on this top: fold-b100's generator scratch/fold-b100/gen_coeff_fold.py extended by the
    generations 46, 47 (TailZ72, TailZ73) and the textbook/added conversions 18 -> 17 -> 16, 27 -> 26 ->
    ZInQKernel/OneProof/H/TailZ74.lean (`sixContactMin_of_open67`, OpenResearchLeaves48: the live research path copied
    with suffix CF, heckePrimeIntegralToRational and gamma1IntegralBasis deleted, the 4 readings replaced by
    `eigenformCoeffFieldFinite_proof`; originals unchanged); kinds rows dropped. No new leaf. Count: 38 -> 36 open;
    H 4/29 on 33 -> 4/27 on 31. Checks (VERIFIED): build +Main +Discharges (16215 jobs); frozenTarget standard axioms;
    check_target.py; only Main.lean modified among existing OneProof modules; OpenStatements 36 (both fields gone);
    DischargesTest rerun, no error; render_open --check ok; crosswalk --check ok; autoform check ok.
42. Reviewer rating (inbox 53, the reviewer q21 rate + verify): igusaGL2DSGalSome LEAF/LEAF, kind published, flag the
    reading text of inbox 53 (no unread marker; must_be_glue false), rated_by "q21-igusa-rate + q21-igusa-verify".
    Provenance: DS is not in the manuscript's bibliography (off-route; folded because it was already done). H 4/27 ->
    5/26 on 31. render_open --check ok, crosswalk --check ok.
43. fold-b105 merged (its checks VERIFIED on its branch; rebuilt here): TailZ75 chevalleyPerfect removed outright
    (fold-chev's bypass regenerated on the coeff-field-tc CF chain; -1 field -1 GLUE), TailZ76 semistab-assembly
    (bostLowerBoundAn, gaudronRemondThm14An -> *SS leaves, pending review), TailZ77 pb-p1 bypass (panPrintedP,
    bergerPrintedVT -> panPrintedF, bergerSurveyF); kinds per the reviewer q22 (inbox 52, 55): panPrintedF published GLUE,
    no "unread"; bergerSurveyF consequence GLUE; Berger locator Thm 0.6 = Thm 5.19. Then jp-an-retype (inbox 54,
    wip/jp-an-retype 21c53772): autofold scratch/leaf-fold33/autofold-jp-an.json -> TailZ78, `sixContactMin_of_open71`:
    javanpeykarThm111 <- javanpeykarThm111An (Thm 1.1.1 + section 2.3 composite as the manuscript cites at L870; cited;
    consequence, reading-risk R3'); mumfordTorsionAlgClosed by PR #54's proof. Count: 36 -> 35 open; H 5/26 on 31 ->
    5/25 on 30. Checks (VERIFIED): build +Main +Discharges (16223 jobs); frozenTarget standard axioms; OpenStatements
    35; DischargesTest rerun, no error; render_open --check ok; crosswalk --check ok; autoform check ok.
44. Reviewer rating (inbox 57, the reviewer q23): deRhamVpAbVarDirect LEAF/LEAF, kind published, flag the AI page read of
    inbox 57 (no unread marker), rated_by "q23-derham-rate + q23-derham-verify"; provenance (b), outside the
    manuscript's bibliography. DeRhamRange.lean imported from OneProof/Main.lean so the built target re-checks
    range_iotaF_eq_bdrFix. H 5/25 -> 6/24 on 30. Build +Main, frozenTarget standard axioms, render/crosswalk --check ok.
