# ci-audit report

Task: make the `autoform verify` workflow pass. It had failed in "Audit every
root-package declaration" on five `partial def`s of meta-level tactic code.

## Status

This task has no blueprint leaves. The table lists the declarations it changed.

| article path | Lean name | status |
|---|---|---|
| (tactic `size`) | `ZInQ.Size.Tac.applyThen`, `tryLemmas`, `unfoldSubject`, `sizeGoal` (ZInQKernel/Size/Majorants/Tactic.lean) | done: total, structural recursion on fuel |
| (tactic `scope`) | `ZInQ.Syntax.Build.scopeGoal` (ZInQKernel/Syntax/Templates/Scope.lean) | done: total, structural recursion on fuel |

The change: each function takes a fuel argument `ℕ` first. It fails with
`size: recursion limit reached` (or `scope: …`) at fuel 0, and every recursive
call passes `fuel` from the arm `fuel + 1`. The four `size` functions remain one
`mutual` block, now compiled by mutual structural recursion. The entry points
(`size`, `size_maj`, `size_le` through `sizeVia`, and `scope`) start with
`sizeFuel = scopeFuel = 100000`. Fuel bounds the nesting depth only, not the
total number of calls, so it never runs out in practice. The behaviour is
otherwise unchanged: same rule dispatch, same backtracking, same error messages.
No proof file was touched, and the clean full build elaborates every use of the
tactics.

## Workflow steps reproduced here, in order

| step | result |
|---|---|
| Validate the theorem DAG (`autoform check blueprint`) | OK: 353 articles, 1201 dependencies (295 fully proved, 22 conditionally proved, 2 ready to prove) |
| Reject kernel-check bypass options (git grep) | passes (no match) |
| Build Lean (`lake translate-config toml`, `--root-package` → `z_in_q_kernel`, `lake check-build`, `lake clean z_in_q_kernel`, `lake build`) | passes, 9481 jobs, 5:18 wall on this machine (2163 s user CPU); largest single Lean process 14.1 GB max RSS |
| Audit (`lake pack`, policy `allowed`, `autoform work assumptions blueprint --json` at the workflow's AUTOFORM_REF, `autoform_audit.py --open-statements`, probe with plain `lean` and `LEAN_ABORT_ON_PANIC=1`, check of the last line) | passes: `kernel trust clean except declared open statements (18994 root-package declaration(s) audited; 5 open statement(s), 10 conditional declaration(s))` |
| Detect statement review | passes. No `blueprint/.autoform-review` marker, no `blueprint/readbacks`, no `review_approved:` key, so review is disabled. |
| Verify statement reviews (`autoform review check blueprint --lean-root .`) | skipped in CI because review is disabled. Run here by hand, it exits 2 with 421 findings (below). |

No further Lean failure appeared after the five `partial def`s were replaced:
the safety and axiom scan, the `lean:` target resolution and the kernel replay
all pass.

### Kernel replay: time and memory

- The whole audit probe (`/usr/bin/time -v lean PROBE`): 7:02 wall, 399 s user
  CPU, 22.4 GB max RSS.
- The replay alone, measured by a copy of the probe that only imports the build
  and calls `autoformAuditKernelReplay`, timed with `IO.monoMsNow`: 414 s
  (6:54) in one run, 363 s in a second. The process's max RSS was 22.3 GB.
  Sampling `/proc/PID/status` showed a peak RssAnon of 15.8 GB and a peak
  RssFile of 6.5 GB (mapped `.olean` files).
- A per-module replay run (each root module replayed onto the environment
  of the previous ones) took 355 s in total. The two base imports alone hold
  8.6 GB of anonymous memory. Nine modules take 277 s:

  | module | replay time | RssAnon after |
  |---|---|---|
  | Model.Heights.SearchKernel | 50.2 s | 14.8 GB |
  | Syntax.Recipes.PowerValue | 48.3 s | 13.7 GB |
  | Syntax.Recipes.Accounting | 30.4 s | 10.7 GB |
  | Compiler.Translation.PowerScope | 25.9 s | 13.1 GB |
  | Compiler.Circuits.PowerTemplateNodes | 25.0 s | 13.7 GB |
  | Syntax.Builder.Recipes | 24.6 s | 13.9 GB |
  | Compiler.Translation.Rational | 24.5 s | 13.7 GB |
  | Syntax.Recipes.Precision | 24.3 s | 13.7 GB |
  | Compiler.Universal.NodeCheck | 24.2 s | 13.7 GB |

  Every other module takes under 8.3 s.

## Statement corrections

None (no leaves).

## Lemmas added beyond the leaves

`ZInQ.Size.Tac.sizeFuel` and `ZInQ.Syntax.Build.scopeFuel`, the default fuel
values.

## Problems

1. **Memory on the CI runner.** The replay needs about 15.8 GB of anonymous
   memory, plus file-backed `.olean` pages. A standard GitHub-hosted
   `ubuntu-latest` runner for a public repository has 16 GB of RAM, so the
   audit step could be killed or thrash there even though it passes here.
   The build step needs less. Its largest Lean process reaches 14.1 GB of
   RSS, mostly mapped `.olean` pages, and the build step already passed in
   CI.
2. **`autoform review check` findings.** CI does not run it while review is
   disabled. Run by hand, it gives 421 findings, none of which a Lean edit in
   this task's scope can fix:
   - 226 `review-source-passage-missing`: the Lean articles cite no exact
     local source passage (`#L<start>-L<end>` in a non-Markdown source). This
     is blueprint content.
   - 54 `review-mapping-drift`: "skeleton declarations () do not match current
     lean metadata", because no review cards exist yet.
   - 136 `review-report-unresolved` of the form "the skeleton probe omitted
     required source for … trusted declaration X.ctorIdx". They involve the
     auto-generated `ctorIdx` of the inductives `Compiler.IR.FExpr`,
     `IR.IExpr`, `Natural.MacroKind`, `Natural.NatNode`, `Natural.VarKind`,
     `RM.Instr`, `Universal.Outcome` and `Syntax.Node`. The skeleton extractor
     at this AUTOFORM_REF finds no source for these compiler-generated
     declarations, which looks like an autoform limitation.
   - 5 `review-report-unresolved` of the form "source lean/ZInQ/….lean is not
     built by any library target": `ZInQ.AlphaPower.alphaZ` and
     `ZInQ.CantorDecoder.{decode, decode5, encode5, pair}` live in the path
     dependency `z_in_q` (`lean/`), which is not a library of the root package.
3. **Resource rule.** My first run of `autoform review check` started up to 8
   `lake env lean` probes in parallel (autoform's `_MAX_PROBE_WORKERS = 8`).
   That broke the one-Lean-process rule; load stayed below 15. I reran it
   under `taskset -c 0`, which gives one worker because autoform reads
   `os.process_cpu_count()`; that run took 44:35 wall and 7.1 GB max RSS.

## Suggestions for the next agent

- If the audit runs out of memory on the hosted runner, the fix is either a
  larger runner (a workflow edit, not allowed to this task) or lighter heavy
  modules. The replay re-checks every `decide +kernel` proof, and the nine
  modules above account for 78% of its time.
- The audit marks four open statements "proof is sorry-free; restate it if
  retracted, then record proof: formalized":
  `ZInQ.Compiler.Universal.haltingCircuit_nodeStats`, `powerTemplate_nodeStats`,
  `powerTemplate_nodes_length` (article halting-node-check) and
  `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck`
  (main/main-theorem). The lead may want to update their articles.
- Before enabling statement review (`blueprint/.autoform-review`), the
  source-passage citations and review cards must be written, and the
  `ctorIdx` and `lean/` extraction findings resolved upstream in autoform.
- To run `autoform review check` with one Lean process at a time, prefix it
  with `taskset -c 0`.
