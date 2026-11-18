# kolyv-weil-fold results

- VERIFIED (Git): base and local `origin/main` are `dcc3d7723`. Cherry-picked all seven additions from `a04588b4f..cfe47c6e7` cleanly; no merge.
- VERIFIED (source): the base's pole call wraps the Cassels–Tate square version. The new supplier retains `casselsTateSquareCurves_of_pairing`, `lemma54At_of_casselsTate`, Selmer corank and simultaneous construction; only the rank supplier changes to `kolyvaginRankOne_of_prints`.
- VERIFIED (earlier print readings, inspected locally): BCDT Introduction (6), p. 3, is at `X₁(N_E)`; the Lean Prop uses `X₀(N_E)` and is GLUE. MPI/90-69 p. 4, Thm. 1, with the p. 3 weak Weil hypothesis, is represented in printed form; current GLUE rating pending the owner's preprint ruling.
- VERIFIED (TSV): main has 31 H fields (strict and strictest 5 LEAF / 26 GLUE), four other binders (1 / 3), and 35 total (6 / 29). Current fold ratings keep all counts; accepting the preprint as LEAF changes the strict four to 2 / 2 and the strict total to 7 / 28.
- VERIFIED (repo tools): the revised spec is valid JSON; stock autofold rejects plain top-level `hK` as not a field of the current bundles. The real headline splice is manual.
- VERIFIED (source closure and Git): the import adds three KolyvWeil modules and five Tau Ceti modules. The five are all in the unchanged `dcc3d7723` vendored tree and in the pin-5a01f5fe selmer-2infty manifest. The compiled import comparison is recorded separately.
- VERIFIED (Git): `git apply --check scratch/kolyv-weil-fold/main-splice.patch` succeeds against the base headline. The base worktree source has not been changed by this patch check.
