# regen-gate-e1: gate of commit e1 of fold/regen-1126e

SHA (git rev-parse HEAD): 87d94d440a31dadd563f1ecc4200e8543dc20063

- Gate 1 (build Main, then Discharges): PASS
- Gate 2 (axioms): PASS
- Gate 3 (frozen hypotheses match the stated effect): PASS
- Gate 4 (OpenStatements + render_open --check): PASS (only "out of date" problems; informational `note:` lines quoted below)
- Gate 5 (vault chapter gen.py): ran, exit 0 (output below)
- Gate 6 (generated files restored; tree clean apart from own files): PASS

## Gate 1
- `lake build ZInQKernel.OneProof.Main`: `Build completed successfully (19939 jobs).` Wall time 15m46s for the run that finished. An earlier run was stopped at job 19709/19939 by the gater's own tool time limit (set too short, about 10 min), with no error before it; lake resumed from there.
- `lake build ZInQKernel.OneProof.Discharges`: `Build completed successfully (2 jobs).` 2.4s.
- No errors.

## Gate 2: axioms (scratch/regen-gate-e1/Axioms.lean, lake env lean)
```
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Gate 3: hypotheses
`#check @ZInQ.OneProof.frozenTarget`: (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves30) hRC hCT hRank, giving 17 + 0 + 2 + 3 = **22 open hypotheses**.

- r : HDec.HSyn.OpenResearchLeaves78, 17 fields: pazukiCor13Upper, dsThm966Printed, afCharpolyDS965, modularHTCoeff, deligneCanonicalModelY3EveryPrint, gaudronRemondSec9LowerAnSS, gaudronRemondThm14AnSS, javanpeykarThm111An, y3FullThreeRepZ30, carayolThmAFrob, shimuraThm1Af, cmHeight62, fowlerProp27PrintCanonical, cmjDegreePrint, silverbergZarhinThm34, **bergerSurveyF** (HDec.PkgI4.PanDict.BergerSurveyF), panThm104F
- t : HDec.HSyn.OpenTextbookLeaves18, `fields: (none)`
- l : HDec.HSyn.OpenAddedLeaves30, 2 fields: colmez1992DeRhamAbVar, fontaine1982HTAbVar
- hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine; hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves; hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne

**Matches the stated effect.** Compared with the parent commit's TailZ105.lean, the only field change is colmezThm01 -> bergerSurveyF. The other 16 fields are unchanged. The regenerated open-statements.json changes in the same way: the colmezThm01 entry becomes bergerSurveyF, and only the panThm104F docstring text changes.

## Gate 4
`lake env lean scripts/one_proof/OpenStatements.lean`: `wrote docs/one-proof/open-statements.json: 22 open hypotheses`

`python3 scripts/one_proof/render_open.py --check` (exit 1, from the out-of-date problems only), verbatim:
```
note: reviews.tsv: pazukiCor13Upper (e1b31749) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition and a verbatim quote
note: reviews.tsv: hRC (181efe5b) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition and a verbatim quote
note: reviews.tsv: hCT (181efe5b) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition and a verbatim quote
note: reviews.tsv: hRank (119a412d) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition
note: reviews.tsv: hRank (fa21b107) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition
note: reviews.tsv: dsThm966Printed (29bfbc3f) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition
note: reviews.tsv: silverbergZarhinThm34 (a728cb72) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition
note: reviews.tsv: hRank (014ea897b) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition
note: reviews.tsv: gaudronRemondSec9LowerAnSS (55cc29bd4) is an AI-READ row from before the real-text rule and lacks a sha256 of the copy read in edition
note: scratch/contrib-kit/DischargesTest-output.txt was made with 24 open hypotheses, the Lean data has 22: rerun scratch/contrib-kit/DischargesTest.lean after the fold
docs/one-proof/OPEN.md is out of date: run python3 scripts/one_proof/render_open.py
docs/one-proof/pages-wanted.md is out of date: run python3 scripts/one_proof/render_open.py
STATUS.md is out of date: run python3 scripts/one_proof/render_open.py
```
The `note:` lines are printed outside the script's problems list and do not affect the exit code. There are no row-check failures and no unclassified hypotheses. The notes are about legacy AI-READ review rows and a stale contrib-kit example output (24 vs 22). Neither comes from this commit's change.

## Gate 5
`python3 -I scripts/one_proof/vault_chapter/gen.py` (exit 0), verbatim:
```
28 files; kinds {'published': 7, 'consequence': 12, 'composite': 0, 'project glue': 0}; removed ['blueprint/roadmap/height-decomposition/abelian-varieties/README.md', 'blueprint/roadmap/height-decomposition/abelian-varieties/tate-module-duality.md', 'blueprint/roadmap/height-decomposition/modular-galois/deligne-representations.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/conrad-local-algebraicity.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/scholze-de-rham-comparison.md']
```
There were no assertions and no other `note:` line. The run added 2 chapter files (untracked): blueprint/roadmap/height-decomposition/p-adic-hodge/colmez-p-adic-periods.md and blueprint/roadmap/height-decomposition/p-adic-hodge/fontaine-hodge-tate-abelian.md. It also modified 24 files under blueprint/: the coverage and sources indexes plus chapter files.

## Gate 6
I restored the generated files with `git checkout -- docs/one-proof/ blueprint/` and removed the two untracked files that gen.py had added. After that, `git status` showed only scratch/regen-gate-e1/ and this report.

Results log: scratch/regen-gate-e1/log.md.
