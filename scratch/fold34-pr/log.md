# fold34-pr log

Base: wip/leaf-fold33b c0f3d085 (= fork main; origin/main did not move). Build tree seeded from ~/dzq-check2
(at c0f3d085); `lake build +ZInQKernel.OneProof.Main` replayed only (14226 jobs), frozenTarget standard axioms.
Base hash dump: scratch/fold34-pr/hashes_base.txt (15751 constants of ZInQKernel.OneProof modules).
render_open count at base: 35 open (29 H, strictest 11/18, 6 others).

## Step 1. Merge fork PR #54 (origin/proof/mumford-torsion-review-20261117, 9f54c2cc)
- `git merge --no-ff` clean (merge-base c1e4ed1b; all 1389 files added, all under ZInQKernel/Contrib/:
  CloudB3W16Torsion, CloudB3W16FiniteGroup, OneProof/MumfordTorsionAlgClosed.lean). Commit 16cd620c.
- LICENSE/NOTICE files kept verbatim: CloudB3W16FiniteGroup/LICENSE, CloudB3W16Torsion/NOTICE.md,
  CloudB3W16Torsion/Vendor/AnthropicFLT/{LICENSE,NOTICE.upstream,ATTRIBUTION.upstream.md},
  .../P2M/Sol/RRSplit/{LICENSE,NOTICE.upstream,ATTRIBUTION.upstream.md,README.md}.
- No scratch files, no host paths (one grep hit "/root/" in prose "degree/root/leaf", not a path).
- Text scan of the 1351 added .lean files (VERIFIED, grep -w): no sorry, admit, native_decide, axiom, opaque, unsafe,
  implemented_by, extern; no skipKernelTC, addDecl, run_cmd, #eval, macro/elab/syntax, import Lean, debug options.
  Imports outside the PR: Mathlib and existing tree vendored modules (CloudW02Connectedness, CloudB2X0Transitive).
- Comment-aware scan (scratch/fold34-pr/tools/scan_lean.py: strips nested block comments, line comments, strings;
  self-tested on a file with sorry/axiom): 1351 files, 0 hits for sorry, admit, native_decide, axiom, opaque,
  unsafe, implemented_by, extern, run_cmd/run_tac/run_elab, addDecl, skipKernelTC, reduceBool, csimp, macro/elab/
  syntax, initialize, #eval, debug.* (VERIFIED).
- Build (VERIFIED): `lake build ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed` succeeded, 10693 jobs, 1343
  modules built, 23 min wall, no error (summary scratch/fold34-pr/build54-summary.txt;
  only warnings: linters). Lake's default target builds only ZInQKernel.lean's import closure, so the 8 PR modules
  the provider does not reach are not built by `lake build ZInQKernel` either.
- `#discharges` (scratch/fold34-pr/Discharges54.lean, output discharges54-output.txt) (VERIFIED):
  `DISCHARGES [OpenTextbookLeaves16.mumfordTorsionAlgClosed] by ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`,
  still assumes `[]`, axioms `[propext, Classical.choice, Quot.sound]`; `#check` prints the type as exactly
  `AvSplit.MumfordTorsionAlgClosed` (no extra hypotheses), and `example : AvSplit.MumfordTorsionAlgClosed := ...`
  elaborates.
- Module-name clashes: none (all new modules are under new directories ZInQKernel/Contrib/CloudB3W16Torsion,
  CloudB3W16FiniteGroup; the one file under an existing directory is the new OneProof/MumfordTorsionAlgClosed.lean).
  Declaration clashes with Main's environment are checked by the fold build (step 2). No vendored file edited.

## Step 2. Autofold mumfordTorsionAlgClosed (textbook bundle) — render_open: 35 -> 34 open (29 -> 28 H)
- `python3 scripts/one_proof/autofold.py scratch/fold34-pr/autofold-mumford.json`: "strict count: 11/18 on 29 ->
  10/18 on 28; strictest 11/18 -> 10/18"; wrote ZInQKernel/OneProof/H/TailZ56.lean (OpenTextbookLeaves17 =
  OpenTextbookLeaves16 without mumfordTorsionAlgClosed, `openTextbookLeaves16_of_OpenTextbookLeaves17` filling it with
  `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`, `sixContactMin_of_open49`), switched Main.lean,
  dropped the kinds row (textbook, published, LEAF/LEAF) and the claims row (cloud batch 2, issue #81).
  No new leaf. The field was LEAF, so the step removes a field (GLUE unchanged at 18).
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ56`: success
  (15579 jobs, 1 min); `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`
  (VERIFIED). No declaration clash between the PR's library and Main's environment (the build would fail on one).
- Hash guard (scratch/fold34-pr/DumpCompact.lean, tools/hashdiff.py; hashdiff_1_mumford.txt) (VERIFIED):
  before 15751, after 15761, only before 0, only after 10 (all in ZInQKernel.OneProof.H.TailZ56), changed 1
  (ZInQ.OneProof.frozenTarget, type+value).
- Closure check (ClosureCheck.lean; closure_1_mumford.txt) (VERIFIED): closure 289644 constants; sorryAx absent;
  AvSplit.MumfordTorsionAlgClosed is in the closure only as the type of the proved provider (no bundle field of
  OpenResearchLeaves31 / OpenTextbookLeaves17 / OpenAddedLeaves25 has it as type); the earlier removed Props
  (SGA3_VIB_3_10(_Nbhd), MumfordGroupLawConn, HomFreeFiniteAlgClosed, HomFreeFinite, MumfordPhiSurjectiveAC,
  PicZeroAbVar, PicZeroSmooth) stay absent.
- OpenStatements.lean regenerated open-statements.json; render_open.py: "28 H hypotheses, strictest 10/18, 6 others";
  render_open.py --check: "ok: 34 open hypotheses, all classified; 4 generated files up to date"; frontier_crosswalk.py
  then --check ok (232 IDs, 25 matched); DischargesTest rerun (output differs only by the bundle rename 16 -> 17 and
  the dropped field); `autoform check blueprint --lean-root .`: "OK: 781 articles, 2343 dependencies", rc 0.
