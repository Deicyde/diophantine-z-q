96953ecad69da94c08ef8e30aca42e155bdf0314

# regen-gate-1: gate of fold/regen-1126c commit 1 (Berger restore)

- Gate 1 (build Main, then Discharges): PASS. Main: 19934 jobs, 1502 s; Discharges: 2 jobs, 3 s. No errors.
- Gate 2 (axioms): PASS.
- Gate 3 (frozen hypotheses): PASS. 22 hypotheses, which matches the stated effect.
- Gate 4 (OpenStatements + render_open --check): PASS. Only "out of date" messages, plus one informational note (quoted below).
- Gate 5 (vault_chapter gen.py): PASS (ran; output below).
- Gate 6 (restore): PASS. After `git checkout -- docs/one-proof/ blueprint/`, git status shows only scratch/regen-gate-1/ (and this report).

## Axiom output
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]

## Hypotheses (count 22)
frozenTarget : OpenResearchLeaves78 → OpenTextbookLeaves18 → OpenAddedLeaves29 →
RestrictedConverseGenuine → CasselsTatePairingCurves → SilvermanAEC_C_16_5_5_RankOne → FrozenTarget

- HDec.HSyn.OpenResearchLeaves78 (17): pazukiCor13Upper, dsThm966Printed, afCharpolyDS965, modularHTCoeff,
  deligneCanonicalModelY3EveryPrint, gaudronRemondSec9LowerAnSS, gaudronRemondThm14AnSS, javanpeykarThm111An,
  y3FullThreeRepZ30, carayolThmAFrob, shimuraThm1Af, cmHeight62, fowlerProp27PrintCanonical, cmjDegreePrint,
  silverbergZarhinThm34, bergerSurveyF (: HDec.PkgI4.PanDict.BergerSurveyF), panThm104F
- HDec.HSyn.OpenTextbookLeaves18 (0): none
- HDec.HSyn.OpenAddedLeaves29 (2): scholzeH1AbVar, t10TateDuality
- bare Props (3): ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine,
  ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves,
  ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne

17 + 0 + 2 + 3 = 22. Matches the stated effect: colmezThm01 is absent, bergerSurveyF : PanDict.BergerSurveyF is in
OpenResearchLeaves78, and the count is 22. OpenStatements.lean also reports "22 open hypotheses".

## render_open.py --check (exit 1)
```
note: scratch/contrib-kit/DischargesTest-output.txt was made with 24 open hypotheses, the Lean data has 22: rerun scratch/contrib-kit/DischargesTest.lean after the fold
docs/one-proof/OPEN.md is out of date: run python3 scripts/one_proof/render_open.py
docs/one-proof/pages-wanted.md is out of date: run python3 scripts/one_proof/render_open.py
STATUS.md is out of date: run python3 scripts/one_proof/render_open.py
```
No row-check or unclassified-hypothesis messages. The "note:" line is informational: render_open.py prints it without
adding it to the problem list. It means the saved example output (unchanged by this commit, last touched in 3d6090a13)
is stale relative to the count of 22. The fold desk may want to regenerate it.

## gen.py
```
29 files; kinds {'published': 6, 'consequence': 13, 'composite': 0, 'project glue': 0}; removed ['blueprint/roadmap/height-decomposition/modular-galois/deligne-representations.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/conrad-local-algebraicity.md']
```
No "note:" line, no assertion. Two chapter files were removed and none added; 26 other blueprint files were modified.

## Throttle deviation
Both `lake build` runs used the full `LEAN_NUM_THREADS=4 systemd-run --user --scope ... MemoryMax=60G nice` wrapper.
For the three `lake env lean` checks (7 s each) the sandbox refused `systemd-run`, so they ran as
`LEAN_NUM_THREADS=4 nice lake env lean ...` without the memory scope. Each ran alone, with load < 10 and ≥ 128 GB available.

Details: scratch/regen-gate-1/log.md.
