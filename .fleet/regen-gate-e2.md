# regen-gate-e2: gate of fold/regen-1126e commit e2 (M1)

SHA (git rev-parse HEAD): 1320587e0e58c5ec8c04e6fd774c38b8ff9a985a

- Gate 1 (build Main, then Discharges): PASS. Main exit 0 after 1492 s, 19949 jobs, no errors. Discharges exit 0 after 3 s.
- Gate 2 (axioms): PASS
- Gate 3 (frozen hypotheses match the stated effect): PASS (21 hypotheses; one note on the modules, below)
- Gate 4 (OpenStatements + render_open --check): PASS (the only problems are "out of date" lines; the other lines are informational notes, quoted below)
- Gate 5 (vault_chapter gen.py): PASS (ran; exit 0; no note: line or assertion)
- Gate 6 (restore generated files): PASS. After git checkout of docs/one-proof and blueprint, and removal of the 2 chapter files gen.py added, git status shows only scratch/regen-gate-e2/ and this report.

## Axioms

```
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Hypotheses: 21

```
ZInQ.OneProof.frozenTarget : HDec.HSyn.OpenResearchLeaves79 →
  HDec.HSyn.OpenTextbookLeaves18 →
    HDec.HSyn.OpenAddedLeaves30 →
      ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine →
        ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves →
          ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne → ZInQ.FrozenTarget
```

- r : OpenResearchLeaves79, 16 fields: pazukiCor13Upper, dsThm966Printed, afCharpolyDS965, modularHTCoeff,
  deligneCanonicalModelY3EveryPrint, gaudronRemondSec9LowerAnSS, javanpeykarThm111An, y3FullThreeRepZ30,
  carayolThmAFrob, cmHeight62, fowlerProp27PrintCanonical, cmjDegreePrint, silverbergZarhinThm34, bergerSurveyF,
  panThm104F, gaudronRemondThm14Printed.
- t : OpenTextbookLeaves18, no fields.
- l : OpenAddedLeaves30, 2 fields: colmez1992DeRhamAbVar, fontaine1982HTAbVar.
- hRC (RestrictedConverseGenuine), hCT (CasselsTatePairingCurves), hRank (SilvermanAEC_C_16_5_5_RankOne).

Comparison with the stated effect: matches. Total 16 + 0 + 2 + 3 = 21. shimuraThm1Af is gone. bergerSurveyF and
gaudronRemondThm14Printed are present. colmezThm01 and gaudronRemondThm14AnSS are absent. t, l, hRC, hCT and hRank
are as stated.

Note on "seven Contrib modules built through Main's imports": all seven exist. Five of them were built in the Main
build: AbVarQuotientFinite, AbVarQuotientComplement, ShimuraQuotientGeometry, ShimuraQuotientImageSum and
AfShimuraProof. **AbVarQuotientConnected and ShimuraQuotientHecke are imported by no module in the tree, so Main does
not build them.** As an extra check, I built each one standalone with `lake build <Module>`: both exit 0 with no errors,
in 13 s and 11 s. AfShimuraProof gives one module-system warning (imports Mathlib.RingTheory.Localization.BaseChange
without `module`).

## render_open --check (exit 1)

`lake env lean scripts/one_proof/OpenStatements.lean`: `wrote docs/one-proof/open-statements.json: 21 open hypotheses`

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
note: scratch/contrib-kit/DischargesTest-output.txt was made with 24 open hypotheses, the Lean data has 21: rerun scratch/contrib-kit/DischargesTest.lean after the fold
docs/one-proof/OPEN.md is out of date: run python3 scripts/one_proof/render_open.py
docs/one-proof/pages-wanted.md is out of date: run python3 scripts/one_proof/render_open.py
STATUS.md is out of date: run python3 scripts/one_proof/render_open.py
```

There are no row-check failures and no unclassified hypotheses. In render_open.py, only the three "out of date" lines go
into the problems list that causes exit 1. The note: lines are printed outside that list: the reviews.tsv notes cover
rows in the script's legacy AI-READ allowlist, and the DischargesTest note is a stale example count (24 -> 21) for the
fold to refresh.

## gen.py (exit 0)

```
27 files; kinds {'published': 7, 'consequence': 11, 'composite': 0, 'project glue': 0}; removed ['blueprint/roadmap/height-decomposition/abelian-varieties/README.md', 'blueprint/roadmap/height-decomposition/abelian-varieties/tate-module-duality.md', 'blueprint/roadmap/height-decomposition/modular-galois/deligne-representations.md', 'blueprint/roadmap/height-decomposition/modular-galois/shimura-abelian-varieties.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/conrad-local-algebraicity.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/scholze-de-rham-comparison.md']
```

gen.py also added 2 chapter files that are untracked at this SHA:
blueprint/roadmap/height-decomposition/p-adic-hodge/colmez-p-adic-periods.md and
.../p-adic-hodge/fontaine-hodge-tate-abelian.md. It modified 23 tracked blueprint files. I restored all of them;
nothing generated is committed.
