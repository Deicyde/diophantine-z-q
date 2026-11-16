# Reproduce Version 18

Use [the 196 guide](196/REPRODUCTION.md) for the selected polynomial and [the 198 guide](198/REPRODUCTION.md) for its complete parent. Both checkers authenticate their source inputs and accept explicit paths; neither executes upstream producer code or needs credentials. The 196 checker uses the Python standard library. The 198 checker additionally needs the pinned SymPy version in its requirements file.

From the repository root, with a fresh output path:

```sh
python -B research/version18/196/checks/independent196.py --source-root research/version18/196/upstream/source --parent-table research/version18/198/upstream/H10-quartic198/circuits/inverse198/quadratic.json --output reproduction-output/196-result.json
```

Expected: `PASS`, 48,690 assertions, all 182 row identities, both deleted defining identities, nonvanishing guards, full expansion and coefficient statistics. The independent parent check has 50,684 assertions. See its guide for the separate source authentication, generator and printed-row roundtrip commands. Choose unused output paths; the tools refuse overwriting their inputs or prior results.

The manuscript profile and CI rebuild are checked with:

```sh
python -B scripts/check_current_manuscript.py
python -B scripts/build_paper.py
```

The committed release PDF uses the actual serial pdfLaTeX build recorded in [BUILD.json](BUILD.json). CI's pinned Tectonic rebuild is a separate engine and need not produce identical PDF bytes. The build checks verify bindings and compilation, not the mathematical theorem. The detailed [build guide](../../docs/current-manuscript-build.md) explains this distinction.

No reproduction command evaluates Busy Beaver. The symbolic table is complete; the manuscript proves that its fixed coefficient specification defines the integers. All arithmetic and parameter-selection dependencies must be reviewed separately from these finite algebra checks.

## Required CI coverage for the current quartics

The `Construction regeneration and finite checks` job now runs the independent 198 reconstruction, its complete printed-row roundtrip, the independent 196 elimination audit, and the 196 printed-row and multiplier roundtrip. The job also checks that both complete row components occur unchanged in `manuscripts/quartic_v18.tex`, and verifies the shifted-square input identity explained in [INPUT-TEST-IDENTITY.md](dependencies/INPUT-TEST-IDENTITY.md). These steps propagate failures and publish their JSON results in the `construction-checks` artifact. This describes the workflow; the actual result is the run attached to the reviewed commit.

The added 196 printed-table command is documented in [its reproduction guide](196/REPRODUCTION.md). To repeat the manuscript binding and input identity checks, run:

```sh
python -B scripts/test_v18_table_binding.py
python -B scripts/check_v18_table_binding.py --root . --report build/version18/current-table-binding.json
```

No theorem statement, manuscript source, PDF or polynomial table changes as part of this CI repair.
