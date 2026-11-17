# fold34-pr: fork PRs #54 and #55 folded (integration)

**Result.** On wip/leaf-fold33b c0f3d085 (35 open hypotheses: 29 H with strict and strictest 11/18, 6 TYZ/GZ), this
task merged two outside contributions, reviewed and built them on this host, and folded each provider into the single
proof by one autofold with no new leaf. The result is **33 open hypotheses: 27 H (strict and strictest 10/17) and the
same 6 TYZ/GZ**. The textbook bundle now has only `charPolyIndepOfEllAlgClosed`.

| step | field (bundle, kinds) | provider (fork PR, branch head) | module | top theorem | render_open |
|---|---|---|---|---|---|
| 2 | mumfordTorsionAlgClosed (textbook, published LEAF) | `ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof` (#54, 9f54c2cc) | TailZ56 | `sixContactMin_of_open49` | 34 open, 28 H, 10/18 |
| 4 | gagaMorphism (textbook, consequence GLUE) | `ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof` (#55, d81efece) | TailZ57 | `sixContactMin_of_open50` | 33 open, 27 H, 10/17 |

Step 2 removes a field (LEAF), step 4 lowers the strict and strictest GLUE count by one. Neither raises a count.

## Review of the contributions (VERIFIED, scratch/fold34-pr/log.md steps 1 and 3)

- **Provider types.** `#check` prints `mumfordTorsionAlgClosed_proof : AvSplit.MumfordTorsionAlgClosed` and
  `gagaMorphism_proof : ZInQ.HomLattice.GAGAMorphism`: exactly the field types, no extra hypotheses; `example` with the
  field type elaborates. `#discharges` (Discharges54.lean, Discharges55.lean, with Main imported) reports each as
  discharging its field with `still assumes: []` and axioms `[propext, Classical.choice, Quot.sound]`.
- **Forbidden constructs.** A comment- and string-aware scan (scratch/fold34-pr/tools/scan_lean.py, self-tested) of
  every added .lean file (1351 for #54, 416 for #55) finds no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`,
  `unsafe`, `implemented_by`, `extern`, `run_cmd`/`run_tac`/`run_elab`, `addDecl`, `skipKernelTC`, `reduceBool`,
  `csimp`, `macro`/`elab`/`syntax`, `initialize`, `#eval` or `debug.` option. With `#print axioms` standard, every
  declaration the providers reach is kernel-checked without `sorryAx` or extra axioms.
- **Builds on this host.** #54's provider: 1343 modules, 23 min; #55's: 398 modules, 17.5 min; no error
  (build54-summary.txt, build55-summary.txt). The libraries reuse the tree's vendored modules (CloudW02Connectedness,
  CloudB2X0Transitive, CloudW07JacobiansCurves, CloudB3W17*).
- **Clashes and vendored files.** Both PRs only add files under `ZInQKernel/Contrib/` (new directories, plus four new
  files in the existing `CloudB3W17GAGA/` and the two provider files in `Contrib/OneProof/`), so there is no
  module-name clash; #55's Stacks port lives under `ZInQKernel.Contrib.CloudB3W17bReduced.Port`. No declaration
  clash: the fold builds import both libraries with Main's whole environment. No existing tree file and no vendored
  file was edited; LICENSE/NOTICE/ATTRIBUTION files are kept verbatim (listed in the log). No scratch files, no host
  paths in the merged trees.

## Checks after each fold (VERIFIED)

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` and the new module; `#print axioms
ZInQ.OneProof.frozenTarget` standard; DumpCompact hash guard (base -> final: only `ZInQ.OneProof.frozenTarget` changed,
19 new constants, all in TailZ56/TailZ57); closure check (298138 constants, no `sorryAx`, no bundle field typed by a
removed Prop, earlier removed Props still absent); `OpenStatements.lean`; `render_open.py` then `--check`;
`frontier_crosswalk.py` then `--check`; `scratch/contrib-kit/DischargesTest.lean` rerun; `autoform check blueprint
--lean-root .` OK (781 articles). kinds.tsv rows dropped: mumfordTorsionAlgClosed, gagaMorphism; claims.tsv rows dropped:
the same two (issues elliotglazer#81, #82); no row added.

## Reproducing on a later head

scratch/fold34-pr/REPLAY.md: merge the two PR branches (add-only), then run `autofold.py` on
`scratch/fold34-pr/autofold-mumford.json` and `autofold-gaga.json`, one at a time, each followed by
`scratch/fold34-pr/checks.sh TAG` and the render/crosswalk/autoform checks. The specs name only the fields and
providers, so they apply to whatever generation the textbook bundle has on that head.
eichler-bound's fold reads both fields: if it is replayed after this one, its spec has to use the two providers in
place of `{t}.mumfordTorsionAlgClosed` and `{t}.gagaMorphism`.

## Not done

- credits.tsv and fold-queue.tsv are not updated (outside this task's files). Suggested credits rows: `mumfordTorsionAlgClosed
  proof` (fork PR #54, fold fold34-pr) and `gagaMorphism proof` (fork PR #55, fold fold34-pr), contributor as recorded
  on the PRs.
- The 8 modules of #54 that the provider does not import are not built (lake's default target builds only
  ZInQKernel.lean's import closure, so the project build does not reach them either).
