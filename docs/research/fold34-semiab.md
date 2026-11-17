# fold34-semiab: height-fix and semiab-descend folded; strict GLUE 18 → 16

Task fold34-semiab, 2026-11-16 to 17. Base: wip/leaf-fold33b `c0f3d085` (= origin/main), top
`sixContactMin_of_open48` (TailZ55). wip/leaf-fold33b fast-forwards to wip/fold34-semiab. The results log is
`scratch/fold34-semiab/log.md`; the replay instructions are `scratch/fold34-semiab/REPLAY.md`. This is model work with
no human review. **VERIFIED** means compiled, computed, or read in a named file on this host.

## 1. Result

| | top | H hypotheses, strictest LEAF/GLUE (render_open) | open hypotheses |
|---|---|---|---|
| base `c0f3d085` | `sixContactMin_of_open48` | 29, 11/18 | 35 |
| fold (TailZ56) | `sixContactMin_of_open49` | **30, 14/16** | 36 |

The fold lowers strict GLUE from 18 to 16 and strictest GLUE from 18 to 16, and it adds one field (VERIFIED by
render_open.py). It is the count semiab-descend reported (−2 GLUE).

The research bundle is now `OpenResearchLeaves32`. It is `OpenResearchLeaves31` without the two consequence/GLUE
fields `bostLowerBound` and `gaudronRemondThm14`, and with three published leaves:

| new field | statement | kinds row |
|---|---|---|
| `bostLowerBoundPrinted` | `ZInQ.HeightFix.BostLowerBoundPrinted`: Bost 1996, the old row verbatim over the printed stable height `IsPrintedStableHeight` | published, LEAF/LEAF |
| `gaudronRemondThm14Printed` | `ZInQ.HeightFix.GaudronRemondThm14Printed`: Gaudron–Rémond 2014 Thm 1.4, likewise | published, LEAF/LEAF |
| `chevalleyPerfect` | `ZInQ.SemiAbDescend.ChevalleyPerfect`: Chevalley's structure theorem over a perfect field, existence and uniqueness (Conrad 2002 Thm 1.1 / Milne AG Thm 8.27, numbers UNVERIFIED) | published, LEAF/LEAF |

Each new row carries the flag "unread: new printed leaf (...); locator UNVERIFIED" (flag_class
`unread,unverified-locator`) and `rated_by` "fold34-semiab; pending review".

The conversion uses three proved inputs:
- `ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley` and `gaudronRemondThm14_of_printed_chevalley`. Their
  arguments are the printed leaf, `uniformizationLeafAll_proof` (proved on this base), the textbook field
  `mumfordTorsionAlgClosed` and `chevalleyPerfect`.
- height-fix's descent glue `SemiAbelianDescendsPerfect`, which `semiAbelianDescendsPerfect_of_chevalley` proves.

So no new GLUE enters.

## 2. Steps

1. **Merge.** wip/height-fix (49e6d97d, which brings height-dict) and wip/semiab-descend (6a6de248) both merged
   cleanly.
   - Five scratch files that redeclare HDec.HSyn bundles are renamed `.lean.txt`: height-dict's `FoldDryRun` and
     `FoldDryRunAll4`, height-fix's `FoldDryRun`, and semiab-descend's `FoldDryRun` and `FoldDryRunCheck`.
   - No host paths were found, and no vendored code or LICENSE/NOTICE files came in.
2. **dict-models.** It is in the base (`Contrib/OneProof/RaynaudSemistableOr.lean`, VERIFIED).
3. **The contributions compile on this base.** These modules build: HeightDictionary (and its three submodules),
   PrintedStableHeight and SemiAbelianDescendsPerfect.
4. **`#discharges`.** Before the fold, both fields are discharged with the standard axioms. The remaining assumptions
   are exactly the printed leaf, `UniformizationLeafAll`, `MumfordTorsionAlgClosed` and `ChevalleyPerfect`.
5. **The spec, regenerated.** `scratch/fold34-semiab/autofold.json` is semiab-descend's spec with the flags above.
   Its dry run gives 11/18 on 29 → 14/16 on 30. The fold itself is autofold's TailZ56, plus one docstring paragraph in
   Main.lean.
6. **Tables.**
   - kinds.tsv drops `bostLowerBound` and `gaudronRemondThm14` (consequence, GLUE/GLUE) and adds the three rows
     above.
   - claims.tsv drops `gaudronRemondThm14` (gr14-narrow, held), which autofold does for every discharged field.
     gr14-narrow's narrower statement can still be restated over the printed height (height-dict §5).

**Optional javanpeykar/pazuki rows: not folded.**
- The 11-16 re-rating of `javanpeykarBound` and `pazukiCor13Upper` cites dictionaries other than the height:
  - for `javanpeykarBound`, the Jacobian/Albanese model dictionary, dim J = genus, and IsBelyiFunction to a Belyi map;
  - for `pazukiCor13Upper`, the polarization dictionary (Appell–Humbert/Lefschetz with GAGA) and the
    IsUniformization clauses.
- The printed-height restatements do not touch those dictionaries, so honest rows for them are "pending reading"
  (GLUE).
- With such rows, the dry run (`autofold-all4-honest.json`) gives the same 14/16 on 30. Neither row lowers the strict
  count, so the rule excludes both.

## 3. Checks (VERIFIED; outputs in `scratch/fold34-semiab/`)

| check | result |
|---|---|
| `lake build +…Main +…Discharges` + TailZ56 + the four new Contrib modules | ok, 14234 jobs |
| `#print axioms` frozenTarget, `sixContactMin_of_open49` | [propext, Classical.choice, Quot.sound] |
| closure (`ClosureCheck.lean`) | 272010 constants. No binder and no bundle field has type `BostLowerBound`, `GaudronRemondThm14` or `SemiAbelianDescendsPerfect`; these remain only as proved intermediate statements. height-dict's superseded leaves, the Props removed by earlier folds, and `sorryAx` are absent. |
| hash guard (DumpCompact over `ZInQKernel.OneProof`) | 15751 → 15784; +33, all in TailZ56; only before 0; changed 1: `ZInQ.OneProof.frozenTarget` |
| OpenStatements | 36 open |
| render_open, --check | 30 H, strictest 14/16, 6 others; ok (STATUS.md, OPEN.md, pages-wanted.md, CONTRIBUTING.md regenerated) |
| frontier_crosswalk, --check | 232 IDs, 24 matched; ok |
| DischargesTest | 36 open, 10010 theorems checked, 41 discharge one |
| `autoform check blueprint --lean-root .` | OK: 781 articles, 705 fully proved, 2531 names resolved |

## 4. What remains

- **Statement checks of the three new leaves against the print** (all flagged unread, locator UNVERIFIED).
  - `ChevalleyPerfect` reads `G/H` as the target of a faithfully flat homomorphism with smooth, connected, affine
    kernel. If a reviewer counts that quotient dictionary, the row becomes a consequence (GLUE).
  - The two height rows rest on height-fix's `IsPrintedStableHeight`, whose metric and semistability definitions
    height-fix proved sound (existence of the measure, and the k(𝔭) ⇒ k̄ ascent).
- **Proposed locators.md rows.** They are proposed in height-fix §5 and semiab-descend; locators.md is not edited here.
- **unipotent-b's `SemiAbelianDescendsSepClosed`** (imperfect, separably closed fields) is not covered by
  `ChevalleyPerfect`. It is not a hypothesis here.
- **javanpeykar-rebase** is a separate later fold and is left out.
