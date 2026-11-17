# fold34-semiab log

Base: wip/leaf-fold33b c0f3d085 (= origin/main; top `sixContactMin_of_open48`, TailZ55; render_open: 35 open, 29 H,
strictest 11/18, 6 others).

1. Merged wip/height-fix (49e6d97d; brings height-dict) and wip/semiab-descend (6a6de248): both clean.
   Hygiene: five scratch files redeclaring HDec.HSyn bundles renamed .lean.txt (height-dict FoldDryRun,
   FoldDryRunAll4; height-fix FoldDryRun; semiab-descend FoldDryRun, FoldDryRunCheck). No host paths in the merged
   files (grep /home/, user name). No vendored code or LICENSE/NOTICE files in either branch.
   dict-models' `ZInQKernel/Contrib/OneProof/RaynaudSemistableOr.lean` is in the base tree (VERIFIED, ls).
2. Build: seeded .lake/build and lean/.lake/build from the shared prebuilt tree dzq-check2 (built at c0f3d085, Main.lean identical).
   Base hash dump `hashes_0_base.txt` (15751 constants; frozenTarget standard axioms) taken before any new build.
   `lake build ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect`: OK (builds HeightDictionary + its three
   submodules, PrintedStableHeight, SemiAbelianDescendsPerfect on this base; only linter warnings)
   (`build_1_contrib.txt`). VERIFIED: height-fix's dependency on dict-models (RaynaudSemistableOr) is met by the base.
3. `#discharges` on the unfolded tree (`Discharges.lean`, output `discharges_0.txt`): `bostLowerBound`,
   `gaudronRemondThm14` discharged by `ZInQ.SemiAbDescend.*_of_printed_chevalley`, still assuming exactly
   [<printed leaf>, UniformizationLeafAll, MumfordTorsionAlgClosed, ChevalleyPerfect], axioms standard. VERIFIED.
   `UniformizationLeafAll` is proved on this base (`_root_.uniformizationLeafAll_proof`), `mumfordTorsionAlgClosed`
   is a field of OpenTextbookLeaves16.
4. Spec regenerated against this tree: `autofold.json` = semiab-descend's spec (the height-fix+semiab one, as
   uniformizationLeafAll is proved here) with the three new leaves flagged "unread: new printed leaf (...); locator
   UNVERIFIED". Dry run (`autofold-dryrun.txt`): strict 11/18 on 29 -> 14/16 on 30; strictest 11/18 -> 14/16
   (GLUE -2, no rise).
   Optional javanpeykar/pazuki rows NOT folded: their 11-16 re-rating cites dictionaries other than the height
   (Jacobian/Albanese model dictionary and Belyi map; polarization dictionary and IsUniformization clauses), which the
   printed-height restatement does not touch, so honest rows are "pending reading" (GLUE). Dry run of
   `autofold-all4-honest.json`: 14/16 on 30, i.e. the same strict count as without them (count-neutral), so the rule
   "only if each lowers the strict count" excludes them.
5. Fold (`autofold.json`, `autofold-run.txt`): TailZ56, `OpenResearchLeaves32` (OpenResearchLeaves31 without
   bostLowerBound, gaudronRemondThm14; with bostLowerBoundPrinted, chevalleyPerfect, gaudronRemondThm14Printed),
   `sixContactMin_of_open49`; Main switched (plus one docstring paragraph). kinds.tsv: rows bostLowerBound,
   gaudronRemondThm14 (consequence, GLUE/GLUE) dropped; three rows added (published, LEAF/LEAF, flag "unread: new
   printed leaf (...); locator UNVERIFIED", flag_class unread,unverified-locator, rated_by "fold34-semiab; pending
   review"). claims.tsv: row gaudronRemondThm14 (gr14-narrow, held) dropped by autofold.
   render_open: base 35 open (29 H, strictest 11/18, 6 others) -> **36 open (30 H, strictest 14/16, 6 others)**;
   strict 11/18 on 29 -> 14/16 on 30. Strict GLUE -2, strictest GLUE -2.
6. Checks (VERIFIED; outputs in this directory):
   - `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` + TailZ56, SemiAbelianDescendsPerfect,
     PrintedStableHeight, HeightDictionary: OK, 14234 jobs (`build_2_fold.txt`).
   - `#print axioms ZInQ.OneProof.frozenTarget` and `HDec.HSyn.sixContactMin_of_open49`: [propext, Classical.choice,
     Quot.sound].
   - Closure (`ClosureCheck.lean`, `closure_1_fold.txt`): 272010 constants; no binder and no field of the three
     bundles has type BostLowerBound, GaudronRemondThm14, SemiAbelianDescendsPerfect (they stay in the closure as
     proved intermediate statements); semiAbelianDescendsPerfect_of_chevalley, ChevalleyPerfect, the two printed
     leaves present; height-dict's superseded printed leaves absent; earlier-removed Props and sorryAx absent.
   - Hash guard (`DumpCompact.lean`, `hashdiff.py`): before 15751, after 15784, only before 0, only after 33 (all
     TailZ56), changed 1 (`ZInQ.OneProof.frozenTarget`) (`hashdiff_1_fold.txt`).
   - `OpenStatements.lean`: 36 open hypotheses.
   - `render_open.py` then `--check`: ok, 36 open, all classified, 4 generated files up to date (STATUS.md, OPEN.md,
     pages-wanted.md, CONTRIBUTING.md regenerated).
   - `frontier_crosswalk.py` then `--check`: ok, 232 IDs, 24 matched (the three new leaves have no frontier ID).
   - `scratch/contrib-kit/DischargesTest.lean` rerun: 36 open, 10010 theorems checked, 41 discharge one.
   - `#discharges` after the fold (`discharges_1_fold.txt`).
   - `autoform check blueprint --lean-root .`: OK, 781 articles, 705 fully proved, 2531 names resolved.
