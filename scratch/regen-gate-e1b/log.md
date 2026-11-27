# regen-gate-e1b results log

Base: fc265aec4f19255353bc7a46fca69e4f1af15c31 (`git rev-parse HEAD`, matches the brief). Tree clean at start.
Load/memory checked before every Lean run (load < 10, > 120 GB available throughout).

| # | command | result | wall |
|---|---------|--------|------|
| 1a | `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build ZInQKernel.OneProof.Main` | stopped by the tool's 10-minute background limit (my timeout setting) at job 19709/19943; no errors in output | ~600 s |
| 1b | same command, resumed | rc=0, "Build completed successfully (19943 jobs)"; 0 `error:` lines (deprecation warnings only) | 987 s |
| 1c | `... nice lake build ZInQKernel.OneProof.Discharges` | rc=0, "Build completed successfully (2 jobs)" | 2 s |
| 2/3 | `lake env lean scratch/regen-gate-e1b/Axioms.lean` (under MemoryMax=60G) | rc=0; axioms [propext, Classical.choice, Quot.sound]; `#check` output in axioms.out | 9 s |
| 3b | `lake env lean scratch/regen-gate-e1b/Fields.lean` (lists bundle fields via getStructureFieldsFlattened) | rc=0; 17 / 0 / 2 fields, see fields.out | 9 s |
| 4a | `lake env lean scripts/one_proof/OpenStatements.lean` | rc=0, "wrote docs/one-proof/open-statements.json: 22 open hypotheses" | 8 s |
| 4b | `python3 scripts/one_proof/render_open.py --check` | rc=1; problems: only 3 "out of date" lines (OPEN.md, pages-wanted.md, STATUS.md); plus 10 advisory `note:` lines (printed, not added to problems; see render.out) | <1 s |
| 5 | `python3 -I scripts/one_proof/vault_chapter/gen.py` | rc=0; 28 files; 5 removed, 2 added chapter files (gen.out, gen-status.out) | <1 s |
| 6 | `git checkout -- docs/one-proof blueprint` + rm of the 2 untracked added chapter files | git status: only scratch/regen-gate-e1b/ | — |

Build outputs (≈19 MB each, warnings only) were not kept.
