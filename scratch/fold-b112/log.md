# fold-b112 log

Base wip/leaf-fold33b d435851d (fork main after lane74; H top `HDec.HSyn.sixContactMin_of_open72`, TailZ79,
`OpenResearchLeaves53`). Build tree `.lake/build` and `lean/.lake/build` copied (reflink) from ~/dzq-wt/lane74
(same commit d435851d, Main.olean of 11-17 10:21).

## 0. Base checks (VERIFIED, 11-17 11:25)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (15975 jobs, replayed); frozenTarget
  [propext, Classical.choice, Quot.sound].
- `bash scratch/lane74/gate.sh`: GATE=ok. `render_open.py --check`: ok, 30 open hypotheses.
- **render_open count at base: 30 open (H 29, strictest 5/24, 1 other).**
- Base hash dump (DumpCompact): 18023 constants (/tmp/fb112/hashes_fold0.txt, not committed).

## Fold 1: bost-gr9 (bostLowerBoundAnSS -> gaudronRemondSec9LowerAnSS; weaker-leaf bypass, count-neutral)

1. Merged origin/wip/bost-gr9 47a34056 (no conflicts; commit af7daff8). Hygiene: `scratch/bost-gr9/GR9Bypass.lean`
   (redeclares HDec.HSyn bundles under HDec.HSyn.GR9) renamed `.lean.txt`; no host paths; no vendored code; no build logs
   on the branch.
2. Finding (base drift): bost-gr9 was written on d67ea55f, where the field was `bostLowerBoundAn`. On this base the field is
   `bostLowerBoundAnSS` (semistab-assembly, fold-b105 fold 2: Bost over `IsAnStableHeightSS`, printed semistability).
   bost-gr9's leaf `GaudronRemondSec9LowerAn` is over `IsAnStableHeight` (`IsSemistableRes`). To keep the printed
   semistability of the sibling rows, new Contrib file `ZInQKernel/Contrib/OneProof/GaudronRemondSection9SS.lean`
   (commit separate from the fold): `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS` (bost-gr9's leaf verbatim with
   `IsAnStableHeight` -> `IsAnStableHeightSS`, as semistab-assembly did for Bost and GR Thm 1.4),
   `gaudronRemondSec9LowerAn_of_ss` (SS leaf => bost-gr9's leaf) and `gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`
   (the replaced field implies the new leaf: never stronger). VERIFIED: builds, the three `#print axioms`
   (`scratch/fold-b112/AxiomsGR9SS.lean`, with `r21_of_sec9An`) are [propext, Classical.choice, Quot.sound].
   Not an on-the-spot statement: it is GR14 section 9 (manuscript bibitem gr2014, cited L894-895) over the printed
   semistability.
3. Closure on this head (`scratch/fold-b112/GR9Closure.lean`, bost-gr9's metaprogram with root `sixContactMin_of_open72`,
   import TailZ79, field forms + `BostLowerBoundAnSS`; 2 min 23 s): 119 affected structures, 90 declarations
   (`gr9-closure.tsv`): TailZ79 3 (`OpenResearchLeaves53`, its conversion to `OpenResearchLeaves36EBCF`,
   `sixContactMin_of_open72`), TailZ74 10 (36EBCF..32EBCF and conversions down to 31), TailZ69 1
   (`sixContactMin_of_open48_eb_k954`), EichlerBoundCopy 76 (identical to bost-gr9's EichlerBoundCopy list, VERIFIED by diff).
4. Generator `scratch/fold-b112/gen_gr9_fold.py` (bost-gr9's gen_bypass.py, regenerated): copies the 89 non-top
   declarations into `HDec.HSyn.GR9` with field types weakened (`HeightSplit.BostLowerBound` -> `GRBostBound`, etc.), the
   field renamed, the reader rewritten to `BostGR9.grBostBound_of_sec9Printed (BostGR9.sec9Printed_of_an
   (BostGR9.gaudronRemondSec9LowerAn_of_ss n.gaudronRemondSec9LowerAnSS) _) _ _ ChevFree.semiAbelianDescendsPerfect_proof`
   (in place of `ChevFree.bostLowerBound_of_printed_free (R3Residual.bostLowerBoundPrinted_of_an
   (SemistabAssembly.bostLowerBoundAn_of_ss n.bostLowerBoundAnSS) _) _ _`) and `HeightSplit.r21_of_leaves'` ->
   `BostGR9.r21_of_grBost'`; the top bundle is emitted in HDec.HSyn as `OpenResearchLeaves54` (27 fields), with the
   javanpeykarThm111An field doc's "semistable reduction as printed" phrase corrected (inbox 62; only in the new structure,
   no existing module edited). Dry run (`GR9DryRun.lean.txt`) compiled: first attempt sorryAx (argument parser dropped a
   `.mumfordTorsionAlgClosed` projection after a parenthesis; fixed), then `sixContactMin_of_open73` standard axioms.
5. `python3 scratch/fold-b112/gen_gr9_fold.py` -> `ZInQKernel/OneProof/H/TailZ80.lean` (3057 lines), Main switched to
   `sixContactMin_of_open73` / `OpenResearchLeaves54` (docstring paragraph added); kinds row `bostLowerBoundAnSS` replaced by
   `gaudronRemondSec9LowerAnSS` (published; flag "pending reading (GR p. 2098 normalization): ... cited inside a proof
   (Lemme 9.1 ...) ... R3' ... remains a step ... provenance cited"; flag_class pending-reading; GLUE/GLUE; packet,
   label, tier, area_issue of the old row); claims.tsv had no row. Count line: strict 5/24 on 29 -> 5/24 on 29.
6. Row edits (inbox 62, 64b) in this fold: 62 (javanpeykarThm111An columns 4 and 7) VERIFIED already applied on the base
   (both replacement texts present verbatim). 64b: the phrase "Berger survey IV.5.1, cited print" is NOT in the
   bergerSurveyF row on this base (grep over docs/, scripts/, OneProof: no hit); the source column's leading survey
   citation ("Berger, An introduction ... IV.5.1 and IV.5.3, with II.2.3, ...; ") is replaced by the lead's text, with
   the survey sections used by the Lean form and the rest of the column kept (`scratch/fold-b112/row_edits_64b.py`).
   Rating unchanged (consequence, GLUE).
7. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ80
   ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS` ok (15978 jobs); `sixContactMin_of_open73` and `frozenTarget`:
   [propext, Classical.choice, Quot.sound].
8. Checks (`run_checks.sh 1 hashes_fold0.txt`, VERIFIED): hash guard 18023 -> 18882, only before 0, only after 859 (all
   in TailZ80), changed only `ZInQ.OneProof.frozenTarget` (`cmp_fold1.txt`). Closure (`FoldCheck-fold1.txt`): 292940
   constants, no sorryAx; `BostLowerBoundAnSS`, `R3Residual.BostLowerBoundAn`, `HeightFix.BostLowerBoundPrinted`,
   `HeightSplit.BostLowerBound`, `bostLowerBoundAn_of_ss`, `ChevFree.bostLowerBound_of_printed_free`,
   `OpenResearchLeaves53`, `sixContactMin_of_open72` absent; `GaudronRemondSec9LowerAnSS`, `gaudronRemondSec9LowerAn_of_ss`,
   `sec9Printed_of_an`, `grBostBound_of_sec9Printed`, `r21_of_grBost'`, `GRBostBound`, `OpenResearchLeaves54`,
   `sixContactMin_of_open73` present. Field check: 27 vs 27 fields, only `bostLowerBoundAnSS` <-> `gaudronRemondSec9LowerAnSS`,
   no other type differs. OpenStatements: 30. render_open + `--check` ok. DischargesTest rerun (17 DISCHARGES lines).
   frontier_crosswalk 232 IDs, 4 matched; `--check` ok. autoform check exit 0 (776 articles, 645 fully proved).
   `scratch/lane74/gate.sh`: GATE=ok. `#discharges` cannot show the field (bypass; the new leaf is weaker); the closure
   check shows it gone.
   **render_open count after fold 1: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**

## Fold 2: sz-raynaud (raynaudSemistableSHOr -> silverbergZarhinThm35; autofold, count-neutral)

1. Merged origin/wip/sz-raynaud 34a0b3cb (no conflicts; commit b67c46ff). Hygiene: build logs `scratch/sz-raynaud/build1.txt`,
   `build2.txt` (163k lines) left out; `scratch/sz-raynaud/DryRunFold.lean` (redeclares an HDec.HSyn bundle) renamed
   `.lean.txt`; no host paths (the home-directory-path hit in `strict/render_open.py` is render_open's own host-path regex); no
   vendored code.
2. `lake build ZInQKernel.Contrib.OneProof.SZRaynaud` ok. `#discharges` on the fold-1 head (`DischargesSZ.lean`, output
   `DischargesSZ-output.txt`, VERIFIED): `OpenResearchLeaves54.raynaudSemistableSHOr` DISCHARGED by
   `SZRaynaud.raynaudSemistableSHOr_of_sz35`, still assumes `[SZRaynaud.SilverbergZarhinThm35]`, axioms standard; all 11
   `#print axioms` of the module standard (pow_smul_tate: [propext, Quot.sound]); no sorry, no error.
3. Spec `scratch/fold-b112/autofold-sz.json` = sz-raynaud's `autofold.json` unchanged (one leaf; `ElliotWildInertiaTrivial`
   is not in the spec, so no row with nothing discharged is added, as inbox 64a asks). Dry run regenerated on this line:
   strict 5/24 on 29 -> 5/24 on 29; the printed module (`SZDryRun.lean.txt`) compiled, `sixContactMin_of_open74` standard axioms.
4. `python3 scripts/one_proof/autofold.py scratch/fold-b112/autofold-sz.json` -> `TailZ81.lean` (`OpenResearchLeaves55`,
   `openResearchLeaves54_of_OpenResearchLeaves55`, `sixContactMin_of_open74`); Main switched; kinds row
   `raynaudSemistableSHOr` (published, LEAF/LEAF) -> `silverbergZarhinThm35` (published, flag "reading 11-17 (...)",
   LEAF/LEAF, flag_class note); claims.tsv no row.
5. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ81` ok
   (15980 jobs); `sixContactMin_of_open74`, `frozenTarget`: [propext, Classical.choice, Quot.sound].
6. Checks (`run_checks.sh 2 hashes_fold1.txt`, VERIFIED): hash guard 18882 -> 18917, only after 35 (all TailZ81), changed
   only `frozenTarget` (`cmp_fold2.txt`). Closure (closure 292974): no sorryAx;
   `SilverbergZarhinThm35`, `raynaudSemistableSHOr_of_sz35`, `OpenResearchLeaves55`, `sixContactMin_of_open74` present
   (`RaynaudSemistableSHOr` stays as the proof's type); fold 1 still in force (`BostLowerBoundAnSS`,
   `HeightSplit.BostLowerBound` absent). Field check 27 vs 27: only `raynaudSemistableSHOr` <-> `silverbergZarhinThm35`.
   OpenStatements 30; render_open + `--check` ok; DischargesTest rerun (16 DISCHARGES lines: the raynaudSemistableSHOr
   discharges are gone with the field); crosswalk ok; autoform exit 0 (776 articles); gate.sh GATE=ok.
   **render_open count after fold 2: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral; LEAF for LEAF).**

## Fold 3: row edits 62 and 64b

Done in fold 1, the first fold that regenerated the docs (log fold 1 item 6): 62 was already applied on the base
(verified); 64b applied by `row_edits_64b.py`. The JavanpeykarAnRetype.lean / TailZ78 / TailZ79 docstrings are not
rebuilt by any fold here, so they are not edited (inbox 62: no build for docstrings alone); the corrected phrase is in
the new structure `OpenResearchLeaves54`'s javanpeykarThm111An field doc (TailZ80), carried by autofold into 55-58.

## Fold 4a: y3-route-a (y3FineModuliAbP -> y3FullThreeRepZ30; autofold, count-neutral)

1. Merged origin/wip/y3-route-a 6558e2ff (brings y3-audit 8dc5f87d; no conflicts; commit d6fcc591). Hygiene: build logs
   `scratch/y3-audit/build1.txt`, `build2.txt`, `build_y3fix.txt`, `scratch/y3-route-a/build-main.txt` left out;
   `scratch/y3-route-a/DryRunFold.lean` renamed `.lean.txt`; no host paths; no vendored code.
2. `lake build ZInQKernel.Contrib.OneProof.Y3FullThreeZ30` ok. `#discharges` on the fold-2 head (`DischargesY3.lean`,
   output `DischargesY3-output.txt`, VERIFIED): `OpenResearchLeaves55.y3FineModuliAbP` DISCHARGED by
   `Y3RouteA.y3FineModuliAbP_of_z30`, still assumes `[Y3RouteA.Y3FullThreeRepZ30]`, standard axioms;
   `y3FineModuliAbP_of_z30`, `y3RepresentableQ_of_z30` standard axioms.
3. Spec `scratch/fold-b112/autofold-y3.json` = the branch's `autofold.json` unchanged. Dry run on this line: 5/24 on 29 ->
   5/24 on 29; printed module (`Y3DryRun.lean.txt`) compiled, `sixContactMin_of_open75` standard axioms.
4. autofold -> `TailZ82.lean` (`OpenResearchLeaves56`, `sixContactMin_of_open75`); Main switched; kinds row
   `y3FineModuliAbP` (consequence, GLUE/GLUE) -> `y3FullThreeRepZ30` (consequence, flag "ELLIOT: ...", GLUE/GLUE,
   flag_class unverified-locator; columns 1-7 identical to the branch's `kinds-row.tsv`, VERIFIED by diff); claims no row.
   On-the-spot item recorded by the branch (relative Lemma P, polarization-free = polarized functor): documented in the
   flag; nothing is built on it.
5. Build (VERIFIED): Main + Discharges + TailZ82 ok (15983 jobs); `sixContactMin_of_open75`, `frozenTarget` standard axioms.
6. Checks (`run_checks.sh 4a hashes_fold2.txt`, VERIFIED): hash guard 18917 -> 18952, only after 35 (all TailZ82), changed
   only `frozenTarget`. Closure 293085: no sorryAx; `Y3FullThreeRepZ30`, `y3FineModuliAbP_of_z30`, `OpenResearchLeaves56`,
   `sixContactMin_of_open75` present; folds 1-2 still in force. Field check 27 vs 27: only `y3FineModuliAbP` <->
   `y3FullThreeRepZ30`. OpenStatements 30; render_open + `--check` ok; DischargesTest rerun (15 lines); crosswalk ok;
   autoform exit 0; gate.sh GATE=ok.
   **render_open count after fold 4a: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**

## Fold 4b: carirr-refold (carayolThmAIrr -> carayolThmAFrob; autofold, count-neutral)

1. Merged origin/wip/carirr-refold a47b51ad (brings carirr-odd 7b1ca2c1 and carayol-herbrand; no conflicts; commit
   8ade4604). Hygiene: build logs `scratch/carayol-herbrand/build1.txt`, `build2.txt`, `scratch/carirr-odd/build-main.txt`,
   `scratch/carirr-refold/build-main.txt` left out; the three `AutofoldDryRun.lean` (redeclare HDec.HSyn bundles) renamed
   `.lean.txt`; no host paths; no vendored code.
2. `lake build ZInQKernel.Contrib.OneProof.CarayolRefold` ok. `#discharges` on the fold-4a head (`DischargesCar.lean`,
   output `DischargesCar-output.txt`, VERIFIED): `OpenResearchLeaves56.carayolThmAIrr` DISCHARGED by
   `CarayolRefold.carayolThmAIrr_of_frob`, still assumes `[CarayolRefold.CarayolThmAFrob]`, standard axioms;
   `carayolThmAIrr_of_frob`, `frob_of_DDT31`, `odd_of_frobDet` standard axioms.
3. Spec `scratch/fold-b112/autofold-car.json` = the branch's `autofold.json` unchanged. Dry run on this line: 5/24 on 29 ->
   5/24 on 29; printed module (`CarDryRun.lean.txt`) compiled, `sixContactMin_of_open76` standard axioms.
4. autofold -> `TailZ83.lean` (`OpenResearchLeaves57`, `sixContactMin_of_open76`); Main switched; kinds row
   `carayolThmAIrr` (consequence, GLUE/GLUE) -> `carayolThmAFrob` (published, flag "unread: new printed leaf (packaged
   form; ...)", GLUE/GLUE, flag_class unread); claims no row.
5. Build (VERIFIED): Main + Discharges + TailZ83 ok (15987 jobs); `sixContactMin_of_open76`, `frozenTarget` standard axioms.
6. Checks (`run_checks.sh 4b hashes_fold4a.txt`, VERIFIED): hash guard 18952 -> 18987, only after 35 (all TailZ83), changed
   only `frozenTarget`. Closure 293169: no sorryAx; `CarayolThmAFrob`, `carayolThmAIrr_of_frob`, `odd_of_frobDet`,
   `OpenResearchLeaves57`, `sixContactMin_of_open76` present; folds 1-4a still in force. Field check 27 vs 27: only
   `carayolThmAIrr` <-> `carayolThmAFrob`. OpenStatements 30. render_open reported "reviews.tsv: 'carayolThmAIrr' is not a
   hypothesis in kinds.tsv": the audit's carayolThmAIrr row moved from reviews.tsv to reviews-retired.tsv (as fold-b105
   did for panPrintedP); then render_open, `--check` ok, crosswalk `--check` ok, gate.sh GATE=ok (rerun after the move).
   DischargesTest rerun (15 lines); autoform exit 0.
   **render_open count after fold 4b: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**

## Fold 5: r3prime-etale + r3prime-bc (R3' proved; flag updates; no field change)

1. Merged origin/wip/r3prime-etale fe330e57 (contains r3prime-bc; no conflicts; commit 2c7bf9c7). Hygiene: no scratch
   .lean redeclares HDec.HSyn bundles (`R3Etale.lean`, `R3BC.lean`, `THGeneric.lean` are development copies in
   ZInQ.R3Etale/R3BC); no host paths; no build logs; no vendored code.
2. `lake build ZInQKernel.Contrib.OneProof.HolChartSerre ZInQKernel.Contrib.OneProof.HolChartBC` ok. `#discharges`
   (`DischargesR3.lean`, output `DischargesR3-output.txt`, VERIFIED): 15 discharges, none by ZInQ.R3Etale / ZInQ.R3BC
   (expected: R3' is a step inside IsAnMetricSq, not a field); `translationAnHol`, `isHolChart_iff_isSerreChart'`,
   `isSerreMetricSq_iff`, `isHolChart_iff_isBCSerreChart`, `ptsHomeomorph`: standard axioms.
3. `python3 scratch/fold-b112/r3prime_flags.py`: R3' caveat replaced by "R3' closed by r3prime-etale + r3prime-bc
   (ZInQ.R3Etale.isHolChart_iff_isSerreChart', ZInQ.R3BC.isHolChart_iff_isBCSerreChart, isSerreMetricSq_iff ...)" in
   the flags of `gaudronRemondSec9LowerAnSS` (what bost-gr9 leaves of bostLowerBoundAnSS), `gaudronRemondThm14AnSS`,
   `javanpeykarThm111An`. Ratings unchanged: each keeps an unread/pending/UNVERIFIED marker (GLUE/GLUE).
4. On-the-spot item (inbox 68): `ZInQ.R3Etale.translationAnHol` (left translation by a complex point is holomorphic for
   Serre's sheaf; proved; GAGA section 2 / SGA 1 XII not in the manuscript's bibliography). No other on-the-spot
   statement added by this fold.
5. Checks (`run_checks.sh 5 hashes_fold4b.txt`, VERIFIED): hash guard 18987 -> 18987, changed 0 (no Lean module in Main's
   closure changed); closure 293169, no sorryAx; OpenStatements 30; render_open + `--check` ok; DischargesTest rerun (15);
   crosswalk ok; autoform exit 0; gate.sh GATE=ok.
   **render_open count after fold 5: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
   The task's rule (a fold lowers the GLUE count or removes a field) is not met by this or any fold here; each was
   folded because the integrator's instructions (inbox 59, 64a, 67, 68) name it as a count-neutral fold.

## Wrap-up
- The four dry-run modules (`GR9DryRun`, `SZDryRun`, `Y3DryRun`, `CarDryRun`; they redeclare HDec.HSyn bundles) renamed
  `.lean.txt`. Report `docs/research/fold-b112.md`, replay `scratch/fold-b112/REPLAY.md`.
- **Final count: 30 open (H 29, strict and strictest 5/24, 1 other), top `sixContactMin_of_open76` (TailZ83,
  `OpenResearchLeaves57`).**
