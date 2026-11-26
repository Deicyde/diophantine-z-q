# regen-gate-1 results log

Base: 96953ecad69da94c08ef8e30aca42e155bdf0314 (git rev-parse HEAD matched before any step). No fetch/merge/rebase.
One Lean process at a time; load < 10 and >= 128 GB available before each run.

| # | Command | Result | Wall |
|---|---------|--------|------|
| 1a | `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build ZInQKernel.OneProof.Main` | exit 0, "Build completed successfully (19934 jobs)"; no errors (linter warnings only) | 1502 s |
| 1b | same wrapper, `lake build ZInQKernel.OneProof.Discharges` | exit 0, "Build completed successfully (2 jobs)" | 3 s |
| 2/3 | `LEAN_NUM_THREADS=4 nice lake env lean scratch/regen-gate-1/Axioms.lean` (#print axioms, #check, #print of the bundles) | exit 0 | 7 s each run (2 runs) |
| 4a | `LEAN_NUM_THREADS=4 nice lake env lean scripts/one_proof/OpenStatements.lean` | exit 0, "wrote docs/one-proof/open-statements.json: 22 open hypotheses" | 7 s |
| 4b | `python3 scripts/one_proof/render_open.py --check` | exit 1; 3 "out of date" messages + one informational note (below) | <5 s |
| 5 | `python3 -I scripts/one_proof/vault_chapter/gen.py` | exit 0 (output below) | <5 s |
| 6 | `git checkout -- docs/one-proof/ blueprint/` | tree clean apart from scratch/regen-gate-1/ | - |

Deviation: on the `lake env lean` calls the sandbox refused `systemd-run`
("Host/namespace escape tools ... can break out of the agent's security sandbox"), so those three runs (each 7 s)
used `LEAN_NUM_THREADS=4 nice` without the systemd scope. The two `lake build` runs did use the full throttle wrapper.

## Axioms (gate 2)
'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]

## #check @ZInQ.OneProof.frozenTarget (gate 3)
```
ZInQ.OneProof.frozenTarget : HDec.HSyn.OpenResearchLeaves78 →
  HDec.HSyn.OpenTextbookLeaves18 →
    HDec.HSyn.OpenAddedLeaves29 →
      ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine →
        ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves →
          ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne → ZInQ.FrozenTarget
```
Bundle fields: OpenResearchLeaves78 has 17 (it includes bergerSurveyF : HDec.PkgI4.PanDict.BergerSurveyF and no colmezThm01);
OpenTextbookLeaves18 has 0; OpenAddedLeaves29 has 2; plus 3 bare Prop hypotheses. Total 22.

## render_open --check (gate 4)
```
note: scratch/contrib-kit/DischargesTest-output.txt was made with 24 open hypotheses, the Lean data has 22: rerun scratch/contrib-kit/DischargesTest.lean after the fold
docs/one-proof/OPEN.md is out of date: run python3 scripts/one_proof/render_open.py
docs/one-proof/pages-wanted.md is out of date: run python3 scripts/one_proof/render_open.py
STATUS.md is out of date: run python3 scripts/one_proof/render_open.py
```
The note is printed directly by render_open.py (lines 638-642) and is not added to `problems`, so it does not set the
exit code. The saved example output was last changed in 3d6090a13, before this commit.

## gen.py (gate 5)
```
29 files; kinds {'published': 6, 'consequence': 13, 'composite': 0, 'project glue': 0}; removed ['blueprint/roadmap/height-decomposition/modular-galois/deligne-representations.md', 'blueprint/roadmap/height-decomposition/p-adic-hodge/conrad-local-algebraicity.md']
```
No "note:" line and no assertion. Diffstat before the restore: 28 files changed, 86 insertions(+), 194 deletions(-)
(26 blueprint files modified, 2 removed, plus open-statements.json); see gen-diffstat.out.
