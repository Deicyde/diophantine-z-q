# fold34-semiab log

Base: wip/leaf-fold33b c0f3d085 (= origin/main; top `sixContactMin_of_open48`, TailZ55; render_open: 35 open, 29 H,
strictest 11/18, 6 others).

1. Merged wip/height-fix (49e6d97d; brings height-dict) and wip/semiab-descend (6a6de248): both clean.
   Hygiene: five scratch files redeclaring HDec.HSyn bundles renamed .lean.txt (height-dict FoldDryRun,
   FoldDryRunAll4; height-fix FoldDryRun; semiab-descend FoldDryRun, FoldDryRunCheck). No host paths in the merged
   files (grep /home/, user name). No vendored code or LICENSE/NOTICE files in either branch.
   dict-models' `ZInQKernel/Contrib/OneProof/RaynaudSemistableOr.lean` is in the base tree (VERIFIED, ls).
2. Build: seeded .lake/build and lean/.lake/build from ~/dzq-check2 (built at c0f3d085, Main.lean identical).
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
