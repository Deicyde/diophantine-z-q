SHA: fc265aec4f19255353bc7a46fca69e4f1af15c31

# regen-gate-e1b: gate of e1b (gr14-printed, Gaudron-Rémond Thm 1.4 as printed, TailZ107)

- Gate 1 (build Main, Discharges): PASS. Main rc=0, 19943 jobs. The first attempt was stopped by a tool time limit at job 19709 with no errors; the resumed run took 987 s. Discharges rc=0, 2 s.
- Gate 2 (axioms): PASS
- Gate 3 (frozen hypotheses vs stated effect): PASS (match)
- Gate 4 (OpenStatements + render_open --check): PASS (only "out of date" problems; advisory notes listed below)
- Gate 5 (vault gen.py): ran, rc=0 (output below)
- Gate 6 (restore): PASS. git status shows only scratch/regen-gate-e1b/ and this report.

## Axioms

```
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Frozen hypotheses: 22 (17 + 0 + 2 + 3)

```
ZInQ.OneProof.frozenTarget : HDec.HSyn.OpenResearchLeaves79 →
  HDec.HSyn.OpenTextbookLeaves18 →
    HDec.HSyn.OpenAddedLeaves30 →
      ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine →
        ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves →
          ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne → ZInQ.FrozenTarget
```

- r : OpenResearchLeaves79 (17): pazukiCor13Upper, dsThm966Printed, afCharpolyDS965, modularHTCoeff,
  deligneCanonicalModelY3EveryPrint, gaudronRemondSec9LowerAnSS, javanpeykarThm111An, y3FullThreeRepZ30,
  carayolThmAFrob, shimuraThm1Af, cmHeight62, fowlerProp27PrintCanonical, cmjDegreePrint,
  silverbergZarhinThm34, bergerSurveyF, panThm104F, gaudronRemondThm14Printed
- t : OpenTextbookLeaves18 (0): none
- l : OpenAddedLeaves30 (2): colmez1992DeRhamAbVar, fontaine1982HTAbVar
- hRC : RestrictedConverseGenuine, hCT : CasselsTatePairingCurves, hRank : SilvermanAEC_C_16_5_5_RankOne

Compared with the stated effect, everything matches: 22 open hypotheses; r has 17 fields with gaudronRemondThm14Printed
and no gaudronRemondThm14AnSS; bergerSurveyF is present and colmezThm01 is absent; t is empty; l = {colmez1992DeRhamAbVar,
fontaine1982HTAbVar}; hRC, hCT and hRank are as at gate e1.

## render_open --check (rc=1)

OpenStatements.lean: `wrote docs/one-proof/open-statements.json: 22 open hypotheses`

Problems (the only lines that set the exit code):
```
docs/one-proof/OPEN.md is out of date: run python3 scripts/one_proof/render_open.py
docs/one-proof/pages-wanted.md is out of date: run python3 scripts/one_proof/render_open.py
STATUS.md is out of date: run python3 scripts/one_proof/render_open.py
```
Advisory notes. The script prints these and does not add them to its problems list. None of them is a row check or an unclassified hypothesis:
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
```

## gen.py (rc=0, verbatim)

```
28 files; kinds {'published': 7, 'consequence': 12, 'composite': 0, 'project glue': 0}; removed ['blueprint/roadmap/height-decomposition/abelian-varieties/README.md', 'blueprint/roadmap/height-decomposition/abelian-varieties/tate-module-duality.md', 'blueprint/roadmap/height-decomposition/modular-galois/deligne-representations.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/conrad-local-algebraicity.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/scholze-de-rham-comparison.md']
```
There was no "note:" line and no assertion. Added (untracked) chapter files: blueprint/roadmap/height-decomposition/p-adic-hodge/colmez-p-adic-periods.md,
blueprint/roadmap/height-decomposition/p-adic-hodge/fontaine-hodge-tate-abelian.md. In total gen.py and OpenStatements touched 30 tracked files
(154 insertions, 363 deletions) plus the 2 added files. The full list is in scratch/regen-gate-e1b/gen-status.out. All of these were restored or removed.
