# Contributing to the Lean proof

This guide covers the current work on the **[Deicyde fork](https://github.com/Deicyde/diophantine-z-q)**. Contributions from people and coding agents are welcome: proofs, mathematical corrections, dependency checks, reviews and reproducibility reports.

## Start here

**Point your coding agent at [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14).** It is the current contributor entry point, with the exact open hypotheses, suggested targets, existing ownership and links to any new tooling.

Paste this prompt into your agent:

> Read https://github.com/Deicyde/diophantine-z-q/issues/14 and follow it. Pick one open statement nobody has claimed, claim it, prove exactly that Lean statement, and open a pull request against Deicyde/diophantine-z-q main.

You can use your own editor, coding agent, subscription or API budget. **No Meta account or agentcloud access is required.** Keep API keys and other credentials private; do not put them in the repository, issue comments, PRs or logs. This contribution path is bringing your own AI usage and returning reviewable work, not depositing keys into a shared token pool.

The [blueprint](https://deicyde.github.io/diophantine-z-q/) shows statements and dependencies. The current assembly is `ZInQ.OneProof.frozenTarget` in [`ZInQKernel/OneProof/Main.lean`](ZInQKernel/OneProof/Main.lean). It still takes open hypotheses: proving a helper or getting green CI does **not** finish the full proof. Use issue #14 for the live list rather than a count copied into this guide.

## Choose and claim one statement

1. Read [issue #14](https://github.com/Deicyde/diophantine-z-q/issues/14), the [ownership tracker #5](https://github.com/Deicyde/diophantine-z-q/issues/5) and relevant issue comments. Check open PRs in both this fork and [the original repository](https://github.com/elliotglazer/diophantine-z-q). Do not reprove work already supplied by an open PR or take a statement someone else owns.
2. Follow issue #14's current claim instructions. For new contributors, comment there with **`Claiming <full Lean statement name>`** before starting. Existing claims on per-target upstream issues remain where they were posted; do not copy one claim into several places or treat an older tracker row as proof that a statement is free.
3. Work on that exact statement. Read its definition and hypotheses in the source, including its fields, base rings, universe parameters, maps and quantifier order. The H-bundle types use namespace `HDec`.
4. If the statement looks wrong or its source cannot be reproduced, explain the precise problem on the issue. Do not silently edit the definition, add assumptions or weaken the conclusion.
5. Post a short update when you finish or release the claim, linking your PR or explaining what remains.

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

Run project commands from the repository root. `lean-toolchain` selects **Lean 4.35.0**, and `lake-manifest.json` pins Mathlib and the other dependencies. Keep those pins unchanged; do not run `lake update` to make a proof compile. The first cache fetch needs network access and disk space for the dependency artifacts.

The root Lake project is the current `ZInQKernel` development tree. The separate `lean/` package is the byte-preserved accepted helper snapshot from the research archive; it is **not a replacement for building your new kernel contribution**.

If you cannot run Lean locally, the public [manual `lean wip` workflow](.github/workflows/lean-wip.yml) supports requested branch builds. You can run workflows on your own fork or ask a maintainer about dispatching one here; dispatch access to this repository is not automatic. That workflow is compiler support, not an AI-agent runner or token service.

## Implement and reuse

- Add a new file under `ZInQKernel/Contrib/YourDir/`, normally importing `ZInQKernel.OneProof.Main` as described in issue #14. Export a named theorem whose type is exactly the claimed hypothesis. Do not provide the desired result as an extra assumption or instance.
- Search existing contributions and libraries before writing a new proof. See the [contribution index](docs/contrib.md). Useful sources include Mathlib, [AxiomMath Stacks](https://github.com/AxiomMath/Stacks), [Mordell](https://github.com/AxiomMath/Mordell), [Anthropic's Fermat project](https://github.com/anthropics/fermats-last-theorem), [Tau Ceti](https://github.com/TauCetiProject/TauCeti) and [openai/math](https://github.com/openai/math).
- Port and bridge genuine proofs to the project's actual objects. Vendor reused code under your own contribution directory, preserve its source revision and license/attribution notices, and document compatibility edits. **Do not add new Lake dependencies.**
- Keep the target definitions, existing assemblies, unrelated contributions and dependency pins untouched. A needed change to a statement or interface must be discussed and identified separately.
- Do not use `sorry`, new axioms, `native_decide`, or kernel-check bypasses to close the claim. A source draft, a compiled theorem, an axiom report and an integrated proof are different results; label them accurately.

## Build your module and inspect its axioms

Build the new module **by name**, replacing the example path with yours:

```sh
lake build +ZInQKernel.Contrib.YourDir.Basic
```

Create a local `ProofCheck.lean` that imports your module and checks the actual exported theorem:

```lean
import ZInQKernel.Contrib.YourDir.Basic

#check YourNamespace.your_statement_proof
#print axioms YourNamespace.your_statement_proof
```

Then run:

```sh
lake env lean ProofCheck.lean
```

The axiom report must contain only `propext`, `Classical.choice` and `Quot.sound`. Also verify that the export has the exact requested type with no extra hypotheses; an axiom report alone does not establish that. Keep compiler warnings and any failed attempts in the evidence rather than presenting an unrun command as a pass.

Before requesting final review, refresh against the current `Deicyde/main` and repeat the relevant checks on the final source. For the root project's default build:

```sh
lake build
```

## Open a focused PR

Commit your contribution to your fork and open a pull request **against `Deicyde/diophantine-z-q` branch `main`**, naming the claimed hypothesis. The project's lead reviews and integrates accepted results into the single assembly.

Include:

- the full Lean statement name, claim/issue link, and base and head commits;
- the exact theorem and any genuinely remaining inputs, plus new dependency or source-port details;
- commands actually run, compilation results, the axiom output, and relevant source hashes/logs;
- what the checks establish and what they do not—especially for computations, audits or conditional wrappers;
- upstream source revisions and preserved third-party notices for reused code;
- the AI tools' contribution, and the independent verification or review performed.

Keep changes focused. Preserve dated research artifacts; create a new version rather than replacing a historical snapshot. Exclude credentials, unrelated private files, dependency caches and generated build trees from the PR. Do not mark the project complete or a hypothesis discharged merely because a draft exists or one helper compiles.

## What CI checks

- [Autoform verification](.github/workflows/autoform-verify.yml) checks the blueprint DAG, builds the root Lake project, audits root-package declarations and checks statement-review evidence under the repository's review policy.
- [Research checks](.github/workflows/research-checks.yml) check finite construction regeneration, the manuscript build and the accepted helper snapshot under `lean/`.
- [Blueprint Pages](.github/workflows/blueprint-pages.yml) builds the site on PRs; deployment follows a verified push to `main`, not a PR or manual site build.
- [Lean WIP](.github/workflows/lean-wip.yml) is a manually dispatched branch build.

A passing workflow proves only its stated checks passed on that commit. It is not independent human review or completion of the full theorem.

For optional local research-package checks, see [docs/building.md](docs/building.md). In particular, `python scripts/check_lean.py` is the archival source/quarantine check, while its `--build` mode checks that package's accepted helpers; neither substitutes for compiling your `ZInQKernel/Contrib/` module. Construction checks need Python 3.11+ and Node.js 22+ and establish finite cases, not the main theorem.

## Mathematical and reproducibility reports

For a manuscript correction, [open an issue in the original repository](https://github.com/elliotglazer/diophantine-z-q/issues/new). For a fork-specific Lean target or implementation problem, use the relevant target issue or the discussion in issue #14.

Give the manuscript date (10/11 or 11/5), release tag or source commit, the theorem/equation/TeX label or file and hash, the exact step at issue, and the relevant definitions and external theorem hypotheses. Supply a counterexample, calculation, proposed repair or precise missing implication when available. Distinguish a false statement from an incomplete justification or unclear exposition.

For a computational certificate, separate how it was found from how it was checked; include input/certificate hashes, checker version, command and output. For every report, distinguish a historical draft, helper, accepted module, conditional assembly and the full intended statement. If AI tools contributed, describe their role and the evidence supplied.
