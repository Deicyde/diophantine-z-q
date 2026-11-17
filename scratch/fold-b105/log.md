# fold-b105 log

Base wip/leaf-fold33b d67ea55f (H top `HDec.HSyn.sixContactMin_of_open67`, TailZ74, `OpenResearchLeaves48`;
render_open: 36 open, H 31, strictest 4/27). Build tree: `.lake/build` and `lean/.lake/build` copied (reflink) from
~/dzq-wt/leaf-fold33b (74395dcf, same Lean sources as d67ea55f, Main.olean of 05:45).
Hash dumps (`DumpCompact.lean`, ~1.7 MB each) are kept out of the commit; the comparisons are `cmp_fold<k>.txt`.

## Fold 1: chevalleyPerfect removed (fold-chev regenerated on the coeff-field-tc copy chain)

1. fold-chev's `gen_bypass.py` stops at `sixContactMin_of_open67` (a let-bound multi-line step whose research
   argument is a nested composite of 16 CF conversions). New generator `scratch/fold-b105/gen_chev_bypass.py` (fold-chev's
   helpers verbatim; new walk): each step may have `let` lines; the nested research argument is applied innermost first
   and the walk stops at the first conversion whose result has no `chevalleyPerfect`; the outer conversions and the final
   call are re-emitted (lets kept). Dry run (VERIFIED): walk `openResearchLeaves46_of_OpenResearchLeaves47_cf -> ... ->
   openResearchLeaves36_of_OpenResearchLeaves37_eb_cf` (11 conversions), stop bundle `OpenResearchLeaves36EBCF` (25
   fields); readers bostLowerBound, gaudronRemondThm14 (both in the CF copy of 37->36) and javanpeykarBound (38->37)
   rerouted to `ZInQ.ChevFree.*_of_printed_free` / `semiAbelianDescendsPerfect_proof`. `OpenResearchLeaves48` (29
   fields) -> `OpenResearchLeaves49` (28). kinds count strict 4/27 on 31 -> 4/26 on 30, strictest 4/27 -> 4/26.
   claims.tsv has no chevalleyPerfect row.
2. `python3 scratch/fold-b105/gen_chev_bypass.py` -> `ZInQKernel/OneProof/H/TailZ75.lean` (copy `TailZ75.lean.txt`):
   `OpenResearchLeaves49`, `openResearchLeaves36EBCF_of_OpenResearchLeaves49 (n) (t : OpenTextbookLeaves18)`,
   `sixContactMin_of_open68` (lets t16, l26; then `sixContactMin_of_open48_eb_k954` through the five CF conversions
   36EBCF -> 31EB). Main switched (import, bundle, top, docstring paragraph); kinds row chevalleyPerfect dropped.
3. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` ok (16217 jobs);
   `sixContactMin_of_open68` and `ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound].
4. Hash guard (VERIFIED, `cmp_fold1.txt`): base dump (run against leaf-fold33b's base oleans) 17984 constants, after 18020;
   only before 0; only after 36, all in `ZInQKernel.OneProof.H.TailZ75`; changed 1: `ZInQ.OneProof.frozenTarget`.
5. Closure (VERIFIED, `FoldCheck-fold1.txt`): closure of frozenTarget 304702 constants; no sorryAx, no
   `ChevalleyPerfect`, `semiAbelianDescendsPerfect_of_chevalley`, `*_of_printed_chevalley`, `OpenResearchLeaves48`,
   `sixContactMin_of_open67`; contains `ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`.
6. OpenStatements: 35 open hypotheses (was 36). render_open: 30 H hypotheses, strictest 4/26, 5 others; `--check` ok.
   DischargesTest rerun (`scratch/contrib-kit/DischargesTest-output.txt`; diff: only `OpenResearchLeaves48` -> `49`
   labels). render_open rerun, `--check` ok. frontier_crosswalk: 232 IDs, 4 matched; `--check` ok.
   autoform check: exit 0, "OK: 776 articles, 2337 dependencies; 701 fully proved" (`autoform-check-fold1.txt`).
   `#discharges` does not list chevalleyPerfect: bypass (no proof of `ChevalleyPerfect`), the field is no longer a
   hypothesis. New statements: none (the new bundle is the old one minus the field).
   **render_open count after fold 1: 35 open (H 30, strictest 4/26).**

## Fold 2: semistab-assembly (bostLowerBoundAn, gaudronRemondThm14An -> printed-semistability leaves; count-neutral)

7. Merged origin/wip/semistab-assembly 41830478 (no conflicts). Hygiene: no scratch .lean redeclares HDec.HSyn bundles
   (`scratch/semistab-assembly/Discharges.lean` only imports and runs `#discharges`); no host paths; no vendored code.
   The contribution `ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean` is kept separate from the fold.
8. `lake build ZInQKernel.Contrib.OneProof.SemistablePrintedReadings` ok; `#discharges` on the fold-1 head
   (`DischargesSemistab.lean`, output `DischargesSemistab-output.txt`, VERIFIED): `OpenResearchLeaves49.bostLowerBoundAn`
   DISCHARGED by `ZInQ.SemistabAssembly.bostLowerBoundAn_of_ss` (still assumes `BostLowerBoundAnSS`),
   `OpenResearchLeaves49.gaudronRemondThm14An` DISCHARGED by `gaudronRemondThm14An_of_ss` (still assumes
   `GaudronRemondThm14AnSS`); standard axioms; the five `#print axioms` of the module standard.
9. Spec `scratch/fold-b105/autofold-semistab.json` = semistab-assembly's `autofold.json` with both leaves kind
   `published` (lead's ruling; the branch had `consequence`) and flags unchanged (both begin "pending review", so GLUE
   by `render_open.must_be_glue`); Gaudron-Remond's flag_class set to `pending-review` (its flag has no UNVERIFIED
   locator; Bost keeps `pending-review,unverified-locator`, display UNVERIFIED). Dry run: 4/26 on 30 -> 4/26 on 30.
10. `python3 scripts/one_proof/autofold.py scratch/fold-b105/autofold-semistab.json` -> `TailZ76.lean` (copy
    `TailZ76.lean.txt`): `OpenResearchLeaves50`, `openResearchLeaves49_of_OpenResearchLeaves50`, `sixContactMin_of_open69`;
    Main switched; kinds rows bostLowerBoundAn, gaudronRemondThm14An -> bostLowerBoundAnSS, gaudronRemondThm14AnSS
    (published, pending review, GLUE/GLUE); no claims rows.
11. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ76`
    ok (16219 jobs); `sixContactMin_of_open69`, `frozenTarget`: standard axioms.
12. Checks (`run_checks.sh 2`, VERIFIED): hash guard 18020 -> 18056, only after 36 (all TailZ76), changed only
    `frozenTarget` (`cmp_fold2.txt`); closure 304765, no sorryAx; open-statements.json has bostLowerBoundAnSS and
    gaudronRemondThm14AnSS, not the old fields; OpenStatements 35; render_open 30 H, strictest 4/26, `--check` ok;
    DischargesTest rerun (18 DISCHARGES lines, no error); crosswalk `--check` ok; autoform check exit 0 (776 articles).
    New statements: `BostLowerBoundAnSS` (Bost, Sem. Bourbaki 795, Asterisque 237 (1996), cited print; display
    UNVERIFIED) and `GaudronRemondThm14AnSS` (Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4, cited print), each the
    old row with semistability as printed; neither is on-the-spot; neither is in diophantine_zq.tex as a Lean-level
    statement (the manuscript cites both results).
    **render_open count after fold 2: 35 open (H 30, strictest 4/26), count-neutral.**

## Fold 3: pb-p1 (panPrintedP, bergerPrintedVT -> panPrintedF, bergerSurveyF; count-neutral)

13. Merged origin/wip/pb-p1 0d4cf145 (no conflicts). Hygiene: `scratch/pb-p1/BypassFold.lean` (redeclares HDec.HSyn
    bundles in `HSyn.PBP1`) and `scratch/pb-p1/FontaineSt.lean` (the source of the Contrib file, same declarations)
    renamed `.lean.txt` (`mkcontrib.py` reads the `.lean.txt`); pb-p1's build-log tails `build1..3.txt` removed; no host
    paths; no vendored code. Contribution `ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean` kept separate (commit
    before the fold).
14. R11 docstring of `PanDict.BergerSurveyF` (PanBergerFontaine.lean, was line 632): "whose Theoreme 0.7 is the same
    theorem" -> "whose Theoreme 0.6 (= Theoreme 5.19 of arXiv:math/0102179v3) is the same theorem (Theoreme 0.7 there is
    Sen's theorem)" (lead's correction; edited in FontaineSt.lean.txt and regenerated with mkcontrib.py; UNVERIFIED by me,
    no network). FINDING: the retired audit row of bergerPrintedV (docs/one-proof/reviews-retired.tsv) records
    "Theoreme 0.7 = Corollaire 5.22" for the Inventiones author copy; pb-p1 read arXiv v3 Thm 0.6 p. 7 as
    "de Rham => potentiellement semi-stable". The two numberings disagree; left for the lead.
15. `lake build ZInQKernel.Contrib.OneProof.PanBergerFontaine` ok; `#discharges` on the fold-2 head (`DischargesPBP1.lean`,
    output `DischargesPBP1-output.txt`, VERIFIED): `OpenResearchLeaves50.bergerPrintedVT` DISCHARGED by
    `PanDict.bergerPrintedVT_of_survey` (still assumes `BergerSurveyF`); `panPrintedP` only by `panPrintedP_of_F` (still
    assumes `BmaxStToFontaine`, not a leaf) or `panPrintedP_of_t`, so the fold is a bypass.
16. Generator `scratch/fold-b105/gen_pbp1_bypass.py` (imports gen_chev_bypass.py's helpers): walk
    `sixContactMin_of_open69 -> openResearchLeaves49_of_OpenResearchLeaves50 -> sixContactMin_of_open68 ->
    openResearchLeaves36EBCF_of_OpenResearchLeaves49`, stop bundle `OpenResearchLeaves36EBCF`; the one reader `r11r12`
    (`panBerger_of_printedPV X.panPrintedP (bergerPrintedV_of_T X.bergerPrintedVT) ...`) rewritten to
    `panBerger_of_F X.panPrintedF X.bergerSurveyF ...` (same DS arguments). Output `TailZ77.lean` (copy
    `TailZ77.lean.txt`): `OpenResearchLeaves51` (28 fields; the two fields replaced in place),
    `openResearchLeaves36EBCF_of_OpenResearchLeaves51`, `sixContactMin_of_open70`; Main switched with a docstring
    paragraph; kinds rows replaced: panPrintedF (published, "pending review; unread: ...", GLUE/GLUE, flag_class
    pending-review,unread), bergerSurveyF (published, "pending review (pb-p1; fold-b105): cited print; ...", no
    'unread', GLUE/GLUE, flag_class pending-review); packet/label/tier/area_issue taken from the replaced rows,
    rated_by "pb-p1 (unreviewed)"; no claims rows. Count 4/26 on 30 -> 4/26 on 30.
17. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ77
    ZInQKernel.Contrib.OneProof.PanBergerFontaine` ok (16221 jobs); `sixContactMin_of_open70`, `frozenTarget` standard.
18. Checks (`run_checks.sh 3`, VERIFIED): hash guard 18056 -> 18092, only after 36 (all TailZ77), changed only
    `frozenTarget` (`cmp_fold3.txt`); closure 304575, no sorryAx, no `PanPrintedP`, `BergerPrintedVT`, `BergerPrintedV`;
    contains `PanPrintedF`, `BergerSurveyF`, `panBerger_of_F`; open-statements.json lists panPrintedF and bergerSurveyF;
    OpenStatements 35. render_open first failed its row check ("reviews.tsv: 'panPrintedP' is not a hypothesis"): the
    audit's panPrintedP row moved to `reviews-retired.tsv` (note line in reviews-retired.md), as for bergerPrintedV in
    batch TailZ72; then render_open 30 H, strictest 4/26, `--check` ok; DischargesTest rerun (17 DISCHARGES lines, no
    error); crosswalk `--check` ok; autoform check exit 0 (776 articles, 701 fully proved).
    New statements: `PanPrintedF` (Pan, arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1 = the manuscript's bibitem
    pan2022, diophantine_zq.tex l. 11041-11045, VERIFIED) and `BergerSurveyF` (Berger, arXiv:math/0210184v1 IV.5.1, a
    cited print of Berger's theorem, cited in the manuscript as berger2002, l. 739/11037). Both cited prints; neither
    on-the-spot. The B1 sketch (pb-p1 report section 4, on-the-spot) is not folded.
    **render_open count after fold 3: 35 open (H 30, strictest 4/26), count-neutral.**

## Replay

19. Text-only replay test (VERIFIED; `REPLAY.md`): temporary worktree at d67ea55f + Contrib files; fake autofold
    (neronOggShafarevichSep, proof with `{t}`), then gen_chev_bypass.py, autofold-semistab.json, gen_pbp1_bypass.py:
    TailZ76/77/78 written, stop bundle 36EBCF each time, readers as above, the fake proof inlined; counts
    4/26 on 30 -> 4/25 on 29 -> 4/25 -> 4/25. Worktree removed (`git worktree remove`).
