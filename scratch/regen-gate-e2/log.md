# regen-gate-e2 results log

Base: 1320587e0e58c5ec8c04e6fd774c38b8ff9a985a (git rev-parse HEAD matched before any step).
Builds ran as `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build ...`,
one Lean process at a time; load stayed below 6 and available memory near 130 GB at every check.

| step | command | result | wall |
|---|---|---|---|
| 1a | `lake build ZInQKernel.OneProof.Main` | exit 0, "Build completed successfully (19949 jobs)", 0 errors (43091 warning lines, all lints) | 1492 s |
| 1b | `lake build ZInQKernel.OneProof.Discharges` | exit 0, "Build completed successfully (2 jobs)" | 3 s |
| 2-3 | `lake env lean scratch/regen-gate-e2/Axioms.lean` (#print axioms, #check, #print of the three bundles) | exit 0; output in axioms.out | 9 s |
| 4a | `lake env lean scripts/one_proof/OpenStatements.lean` | exit 0, "wrote docs/one-proof/open-statements.json: 21 open hypotheses" | 8 s |
| 4b | `python3 scripts/one_proof/render_open.py --check` | exit 1; problems = only the 3 "out of date" lines; plus informational note: lines (render.out) | <1 s |
| 5 | `python3 -I scripts/one_proof/vault_chapter/gen.py` | exit 0; output in gen.out | <1 s |
| 6 | `git checkout -- docs/one-proof blueprint`; removed the 2 untracked chapter files gen.py created | git status: only scratch/regen-gate-e2/ | - |
| extra | `lake build ZInQKernel.Contrib.OneProof.AbVarQuotientConnected` | exit 0 | 13 s |
| extra | `lake build ZInQKernel.Contrib.OneProof.ShimuraQuotientHecke` | exit 0 | 11 s |

New Contrib modules of this commit: in the Main build log, AbVarQuotientFinite, AbVarQuotientComplement,
ShimuraQuotientGeometry, ShimuraQuotientImageSum and AfShimuraProof were built.
AbVarQuotientConnected and ShimuraQuotientHecke are imported by no module in the tree, so they are not built through
Main's imports; built standalone above, both are clean.

Axioms: `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.

frozenTarget hypotheses: r : OpenResearchLeaves79 (16 fields), t : OpenTextbookLeaves18 (no fields),
l : OpenAddedLeaves30 (2 fields), RestrictedConverseGenuine, CasselsTatePairingCurves,
SilvermanAEC_C_16_5_5_RankOne. 16 + 0 + 2 + 3 = 21, which matches the JSON count.
