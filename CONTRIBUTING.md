# Contributing to the Lean proof

This guide covers the current work on the **[Deicyde fork](https://github.com/Deicyde/diophantine-z-q)**. Contributions from people and coding agents are welcome: proofs, mathematical corrections, statement checks, dependency checks, reviews and reproducibility reports.

## Start here

**Point your coding agent at [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14).** It is the current contributor entry point and the one place to claim a Lean statement, with links to the open list, the guides and any new tooling.

The open hypotheses are listed, with their exact Lean types and who holds each, on the generated board [`docs/one-proof/OPEN.md`](docs/one-proof/OPEN.md); the short contract for a proof is [`docs/one-proof/CONTRIBUTING.md`](docs/one-proof/CONTRIBUTING.md).

Paste this prompt into your agent:

> Read https://github.com/Deicyde/diophantine-z-q/issues/14 and follow it. Pick one open statement nobody has claimed, claim it, prove exactly that Lean statement, and open a pull request against Deicyde/diophantine-z-q main. Follow the "Running an AI agent" rules in https://github.com/Deicyde/diophantine-z-q/blob/main/CONTRIBUTING.md.

You can use your own editor, coding agent, subscription or API budget. **No special account or access is required.** Keep API keys and other credentials private; do not put them in the repository, issue comments, PRs or logs. This contribution path is bringing your own AI usage and returning reviewable work, not depositing keys into a shared token pool.

The [blueprint](https://deicyde.github.io/diophantine-z-q/) shows statements and dependencies. The current assembly is `ZInQ.OneProof.frozenTarget` in [`ZInQKernel/OneProof/Main.lean`](ZInQKernel/OneProof/Main.lean). It still takes open hypotheses: proving a helper or getting green CI does **not** finish the full proof. Use OPEN.md's count line for the live figure rather than a count copied into this guide.

No Lean? You can check a Lean statement against its printed source: see [`docs/one-proof/STATEMENT-CHECKS.md`](docs/one-proof/STATEMENT-CHECKS.md).

## Choose and claim one statement

1. Read [`docs/one-proof/OPEN.md`](docs/one-proof/OPEN.md): its status column shows who holds each statement, and its Good first targets section lists suggested starting points. Then claim on [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14) with the claim line below. Check open PRs in both this fork and [the original repository](https://github.com/elliotglazer/diophantine-z-q). Do not reprove work already supplied by an open PR or take a statement someone else holds.
2. Claim before starting. Comment on issue #14 with one line:

   ```text
   Claiming <field> at <commit>
   ```

   `<field>` is the Lean field name exactly as OPEN.md shows it (case-sensitive; backticks around it are fine), and `<commit>` is the `Deicyde/main` commit you start from (recommended, not required). A frontier ID from `docs/research/frontier.md` (such as H-101) in place of the field also counts; it is mapped to the field through `docs/one-proof/frontier-crosswalk.tsv`. Instead of a comment you may open a draft pull request against `Deicyde/diophantine-z-q` that links issue #14 and has the same line in its body. Older claims on the per-area upstream issues (elliotglazer/diophantine-z-q #37, #74, #76 and #78 to #86) stay valid where they were posted; do not copy one claim into several places.
   - **One claim to start.** Hold one open claim at a time until your first contribution is merged. Sub-lemmas you take under another holder's claim, with their agreement, do not count.
   - **Releasing.** If you stop, comment `Releasing <field>: <what blocked you>`. The claim is released at once, and the note helps the next person.
   - **Progress.** `Progress <field>: <text>` is optional; any comment you make on the claim thread counts as activity.
   - **Lapse.** A claim with no public activity for 14 days gets one ping; with no reply 7 days after the ping, the claim is released. A draft PR that keeps receiving commits does not lapse.
   - A project brief or reservation is not a hold: OPEN.md shows such a row as "project interest, free to claim".
3. Work on that exact statement. Read its definition and hypotheses in the source, including its fields, base rings, universe parameters, maps and quantifier order. The H-bundle types use namespace `HDec`.
4. If the statement looks wrong or its source cannot be reproduced, explain the precise problem on the issue. Do not silently edit the definition, add assumptions or weaken the conclusion. A statement shown to be false, vacuous or stronger than its source, with a corrected statement, is a credited result.
5. Post a short update when you finish or release the claim, linking your PR or explaining what remains.

## Editions

The open list is published in editions; once an edition is cut, OPEN.md's header names it and the commit it was cut at. During an edition, a claimed statement is not restated without the holder's agreement. There are two exceptions: a repair of a statement found false, and a narrowing already shown as pending in the statement's OPEN.md row. Every restatement keeps the old form reachable through a conversion theorem, so a proof of the old form still counts.

## Set up the current project

Install [elan](https://github.com/leanprover/elan), fork this repository on GitHub, and clone **your fork**. Replace `YOUR-GITHUB-USER` and `short-statement-name` below.

```sh
git clone https://github.com/YOUR-GITHUB-USER/diophantine-z-q.git
cd diophantine-z-q
git remote add upstream https://github.com/Deicyde/diophantine-z-q.git
git fetch upstream main
git switch -c proof/short-statement-name upstream/main
lake exe cache get
```

Run project commands from the repository root. `lean-toolchain` selects **Lean 4.35.0**, and `lake-manifest.json` pins Mathlib and the other dependencies. Keep those pins unchanged; do not run `lake update` to make a proof compile. The first cache fetch needs network access and disk space for the dependency artifacts. `lake exe cache get` fetches only Mathlib's compiled files; this project's own files build from source.

The root Lake project is the current `ZInQKernel` development tree. The separate `lean/` package is the byte-preserved accepted helper snapshot from the research archive; it is **not a replacement for building your new kernel contribution**.

You do not need to build anything to contribute. For a pull request into `main` that only adds files under `ZInQKernel/Contrib/OneProof/`, the discharge check runs on the files it adds, built on top of the current `main`, as the GitHub Actions check "discharge check" on a fresh hosted runner with no secrets and no access to project machines ([`scripts/one_proof/sandbox/README.md`](scripts/one_proof/sandbox/README.md)). The verdict is in the check's job summary, and the run may wait for a maintainer to approve it before it starts. A pull request that changes anything else is out of scope for the automatic check. The automatic check is being set up: until it has run on a first contribution, include your own `#discharges` output in the pull request. The automatic result is advisory; the project's agents check every pull request before it is merged. The other checks do not compile `ZInQKernel/Contrib/OneProof`, so their green marks say nothing about a contribution. If you want to build locally, the measured costs are in the build-cost table of [`docs/one-proof/CONTRIBUTING.md`](docs/one-proof/CONTRIBUTING.md#what-it-costs-to-build).

## Implement and reuse

- Add a new file `ZInQKernel/Contrib/OneProof/<StatementName>.lean` (helpers may go in a directory next to it), importing the module that defines the statement (never `ZInQKernel.OneProof.Main`: once your file is folded, `Main` imports it). Export a named theorem whose type is exactly the claimed hypothesis. Do not provide the desired result as an extra assumption or instance. Run `#discharges` (`ZInQKernel/OneProof/Discharges.lean`, see `docs/one-proof/CONTRIBUTING.md`) on your file if you can afford the build: it lists the open hypotheses your theorems prove and their axioms.
- Avoid code that runs at build time (`#eval`, `run_cmd`, `initialize`, new `syntax`, `notation`, macros or elaborators). If your file needs it, say why in the PR; a person then reads the file before the check result counts.
- Search existing contributions and libraries before writing a new proof. See the [contribution index](docs/contrib.md). Useful sources include Mathlib, [AxiomMath Stacks](https://github.com/AxiomMath/Stacks), [Mordell](https://github.com/AxiomMath/Mordell), [Anthropic's Fermat project](https://github.com/anthropics/fermats-last-theorem), [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and [openai/math](https://github.com/openai/math).
- Port and bridge genuine proofs to the project's actual objects. Vendor reused code under your own contribution directory, preserve its source revision and license/attribution notices, and document compatibility edits. **Do not add new Lake dependencies.**
- Keep the target definitions, existing assemblies, unrelated contributions and dependency pins untouched. A needed change to a statement or interface must be discussed and identified separately.
- Do not use `sorry`, new axioms, `native_decide`, or kernel-check bypasses to close the claim. A source draft, a compiled theorem, an axiom report and an integrated proof are different results; label them accurately.

## Build your module and inspect its axioms

Build the new module **by name**, replacing the example path with yours:

```sh
lake build +ZInQKernel.Contrib.OneProof.<StatementName>
```

Create a local `ProofCheck.lean` that imports your module and checks the actual exported theorem:

```lean
import ZInQKernel.Contrib.OneProof.<StatementName>

#check YourNamespace.your_statement_proof
#print axioms YourNamespace.your_statement_proof
```

Then run:

```sh
lake env lean ProofCheck.lean
```

The axiom report must contain only `propext`, `Classical.choice` and `Quot.sound`. Also verify that the export has the exact requested type with no extra hypotheses; an axiom report alone does not establish that. Keep compiler warnings and any failed attempts in the evidence rather than presenting an unrun command as a pass.

Before requesting final review, refresh against the current `Deicyde/main` and repeat the relevant checks on the final source. For the root project's default build (which does not compile `ZInQKernel/Contrib/OneProof`):

```sh
lake build
```

## Open a focused PR

Commit your contribution to your fork and open a pull request **against `Deicyde/diophantine-z-q` branch `main`**, naming the claimed hypothesis. The merge bar is in [`docs/one-proof/CONTRIBUTING.md`](docs/one-proof/CONTRIBUTING.md#how-to-check-it); the project's integrator merges a pull request that meets it and folds accepted results into the single assembly.

Include:

- the full Lean statement name, claim/issue link, and base and head commits;
- the exact theorem and any genuinely remaining inputs, plus new dependency or source-port details;
- commands actually run, compilation results, the `#discharges` lines (needed until the automatic check has run on a first contribution; afterwards, if you have them), the axiom output, and relevant source hashes/logs;
- what the checks establish and what they do not, especially for computations, audits or conditional wrappers;
- upstream source revisions and preserved third-party notices for reused code;
- the AI tools' contribution, and the independent verification or review performed.

Keep changes focused. Preserve dated research artifacts; create a new version rather than replacing a historical snapshot. Exclude credentials, unrelated private files, dependency caches and generated build trees from the PR. Do not mark the project complete or a hypothesis discharged merely because a draft exists or one helper compiles.

## Running an AI agent

You are welcome to run an agent on a claim. The rules:

- A named person operates each claim and answers review questions.
- One open claim per operator until the first merge.
- The agent claims in public on issue #14, like anyone else.
- The PR says which model was used, what it did and what the operator checked, and includes the `#discharges` lines and the `#print axioms` output.
- The agent adds files only under `ZInQKernel/Contrib/OneProof/` and edits nothing else. It never changes a statement.
- No build-time code without a stated reason in the PR.
- A reduction to printed theorems cites the edition and page actually read; where nobody read the source, the locator is marked UNVERIFIED.
- A release states its blocker (`Releasing <field>: <what blocked you>`).
- Readings produced by an agent are recorded as AI-READ evidence and never clear a flag; see [`docs/one-proof/STATEMENT-CHECKS.md`](docs/one-proof/STATEMENT-CHECKS.md).

Credit goes to the operator, marked AI-assisted. Good fits: reducing a GLUE hypothesis to theorems in their printed form, and ports from the libraries listed above with their notices kept.

## What CI checks

- [Main build cache](.github/workflows/main-build-cache.yml) builds `+ZInQKernel.OneProof.Main` and `+ZInQKernel.OneProof.Discharges` after a push to `main` that changes Lean, starting from the previous build of `main`. When the build finishes, it fails unless the axioms of `ZInQ.OneProof.frozenTarget` are among `propext`, `Classical.choice` and `Quot.sound`. A build that stops at its time limit saves its progress and reports failure. It is the only hosted check of the headline theorem; until one of its runs passes, that theorem has been compiled only on the project's own machines.
- [Research checks](.github/workflows/research-checks.yml) check finite construction regeneration, the manuscript build and the accepted helper snapshot under `lean/`.
- [Blueprint Pages](.github/workflows/blueprint-pages.yml) builds the site on PRs; deployment follows a passing main build cache run on a push to `main`, not a PR or manual site build.
- [Lean WIP](.github/workflows/lean-wip.yml) is a manually dispatched build of the default target.

Only the main build cache compiles the modules under `ZInQKernel/Contrib/OneProof` that the proof imports, and only on `main`. A passing workflow proves only its stated checks passed on that commit. It is not independent human review or completion of the full theorem. For a contribution, the automatic result is the check "discharge check" on the PR, with its verdict in the job summary; it is advisory, and the project's agents check every file before it is merged (no person reads every file).

For optional local research-package checks, see [docs/building.md](docs/building.md). In particular, `python scripts/check_lean.py` is the archival source/quarantine check, while its `--build` mode checks that package's accepted helpers; neither substitutes for compiling your `ZInQKernel/Contrib/` module. Construction checks need Python 3.11+ and Node.js 22+ and establish finite cases, not the main theorem.

## Checking statements without Lean

The kernel cannot see whether a Lean statement says what its printed source says. If you read the literature but not Lean, [`docs/one-proof/STATEMENT-CHECKS.md`](docs/one-proof/STATEMENT-CHECKS.md) explains how to pick a reading packet from OPEN.md, claim it, and report what the print says. A packet is claimed on its own issue if it has one; otherwise on the statement-checks issue; until that issue exists, on [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14).

## Mathematical and reproducibility reports

For a manuscript correction, [open an issue in the original repository](https://github.com/elliotglazer/diophantine-z-q/issues/new). For a fork-specific Lean target or implementation problem, use the area issue linked in the statement's OPEN.md row or the discussion in issue #14.

Give the manuscript date (10/11 or 11/5), release tag or source commit, the theorem/equation/TeX label or file and hash, the exact step at issue, and the relevant definitions and external theorem hypotheses. Supply a counterexample, calculation, proposed repair or precise missing implication when available. Distinguish a false statement from an incomplete justification or unclear exposition.

For a computational certificate, separate how it was found from how it was checked; include input/certificate hashes, checker version, command and output. For every report, distinguish a historical draft, helper, accepted module, conditional assembly and the full intended statement. If AI tools contributed, describe their role and the evidence supplied.

## Who answers

Replies, reviews and posted checks from the project may be written by AI agents that the project runs; each one carries a note saying so. Jack McCarthy is accountable for them.
