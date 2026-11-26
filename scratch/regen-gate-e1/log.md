# regen-gate-e1: results log

Base: 87d94d440a31dadd563f1ecc4200e8543dc20063 (`git rev-parse HEAD` confirmed before any step). No fetch, merge or rebase.
Host load before each Lean run: load average 2-7, about 127-129 GB available memory (below every hold threshold).
Builds run as `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build ...`; checks as `systemd-run --user --scope -q -p MemoryMax=60G nice lake env lean ...`. One Lean process at a time.

## Gate 1: builds
| command | result | wall time |
|---|---|---|
| `lake build ZInQKernel.OneProof.Main` (run 1) | stopped by the tool's background limit (the gater set a 10 min limit by mistake) at job 19709/19939 (last line `Built ZInQKernel.Contrib.TYZGenus.ShimuraMain`); no error before the stop | ~10 min |
| `lake build ZInQKernel.OneProof.Main` (run 2, incremental resume) | exit 0, `Build completed successfully (19939 jobs).`; no `error`/`✖` lines in either run | 15m45.8s |
| `lake build ZInQKernel.OneProof.Discharges` | exit 0, `Build completed successfully (2 jobs).` | 0m2.4s |

Main's own `#print axioms` line in the build: `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Gates 2-3: scratch/regen-gate-e1/Axioms.lean (`lake env lean`, exit 0, 0m9.1s)
File: `import ZInQKernel.OneProof.Main`, `#print axioms ZInQ.OneProof.frozenTarget`, `#check @ZInQ.OneProof.frozenTarget`, `#print` of the three bundles.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Signature: `OpenResearchLeaves78 → OpenTextbookLeaves18 → OpenAddedLeaves30 → RestrictedConverseGenuine → CasselsTatePairingCurves → SilvermanAEC_C_16_5_5_RankOne → ZInQ.FrozenTarget`.
- OpenResearchLeaves78: 17 fields (listed in the report); OpenTextbookLeaves18: `fields: (none)`; OpenAddedLeaves30: 2 fields.
- Count: 17 + 0 + 2 + 3 = 22. Compared field by field with `git diff HEAD~1 HEAD -- ZInQKernel/OneProof/H/TailZ105.lean`: the only change is `colmezThm01` -> `bergerSurveyF` (docstrings of it and panThm104F change).

## Gate 4
- `lake env lean scripts/one_proof/OpenStatements.lean`: exit 0, 0m8.6s, `wrote docs/one-proof/open-statements.json: 22 open hypotheses`. The JSON diff swaps the colmezThm01 entry for bergerSurveyF (type `HDec.PkgI4.PanDict.BergerSurveyF`) and changes the panThm104F docstring; nothing else.
- `python3 scripts/one_proof/render_open.py --check`: exit 1. Its problems list has only the three "out of date" lines (OPEN.md, pages-wanted.md, STATUS.md). It also prints `note:` lines, which the script prints outside the problems list (informational; they do not set the exit code). Output quoted in the report.

## Gate 5
- `python3 -I scripts/one_proof/vault_chapter/gen.py`: exit 0, 0m0.17s. Output quoted in the report. Tree after: 24 modified chapter files in blueprint/, 5 deleted, 2 new (untracked).

## Gate 6
- `git checkout -- docs/one-proof/ blueprint/`, then removed the two untracked files gen.py created (`blueprint/roadmap/height-decomposition/p-adic-hodge/colmez-p-adic-periods.md`, `.../fontaine-hodge-tate-abelian.md`). `git status --short` after: only `?? scratch/regen-gate-e1/` (the report under .fleet/ was written later).
