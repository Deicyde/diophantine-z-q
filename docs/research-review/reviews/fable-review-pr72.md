# Review of PR 72: budget warnings and kernel-build skip

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.
Reviewed: commit `73f4dc78` on `codex/review-budget-and-kernel-scope` (10 files), against `main` at `81ecf0b5`.

**Decision: accepted for merge.** Both changes do what was asked, and both fail safe.

**Independence.** Independent of the code. I specified both changes, so I am not independent of the approach.

**How I reviewed.** Read the full diff. Ran the committed tests: 48 gate tests and the kernel-scope tests, all passing, no network. Re-ran my budget probe on the new gate script, and ran the skip rule against 25 sample paths using the PR's `KERNEL_CONTRACT.json`. Checked what the kernel scripts and contract actually read. No model API was called and the kernel build was not run.

## Change 1: budget warnings

**Fixed as requested.** A read that would exceed the budget now returns an error to the reviewer with the remaining allowance, and the review continues. Every tool result carries the remaining allowance. Calls in one batch share one projection of the next request. Rejected reads are not counted as sources read, and a rejected `read_history` does not count as history read. The pre-request guard remains as the last defence.

Probe, same scenarios as my PR 71 review:

| Reading pattern | PR 71 | PR 72 |
|---|---|---|
| One 1,000-line read per turn | Aborted before turn 11 | Ran all 46 turns; 10 reads accepted, the rest refused with a warning |
| Two per turn | Aborted before turn 5 | Ran all 23 turns; 10 accepted |
| Four per turn | Aborted before turn 2 | Ran all 12 turns; 12 accepted |
| Six in the first turn | Aborted before turn 2 | Ran all 8 turns; 12 accepted |

The ceiling is unchanged: a reviewer can take in roughly a fifth of the current manuscript per review. That is a consequence of the 400,000 budget, not of this change.

## Change 2: kernel-build skip

**Accepted.** The job keeps its required name and runs on every pull request. A first step, run before checkout, lists the PR's changed files through the API and skips the build only on an explicit, successful "no kernel input changed" decision. Pushes to `main`, manual runs, any error, an incomplete or changing file list, and any unclassified path all build.

The rule is conservative. From my probe:

| Skips the build | Forces the full build |
|---|---|
| `README.md`, `CREDITS.md`, `PROJECT.md`, other `.md` outside `tests/` | Any `.lean` file anywhere; `ZInQKernel/`, `lean/`, `ThirdParty/` |
| Manuscript `.tex` and `.pdf` | `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `KERNEL_CONTRACT.json` |
| `.github/workflows/protocol-b.yml`, the reviewer instructions, `tests/protocol_b/*.py` | Everything under `scripts/`; any file the contract pins (943 files) |
| | `.gitattributes`, the kernel workflow, every other workflow |
| | Any `.json`, `.py`, `.txt` or other non-document file, including `docs/current-manuscript.json` and the quartic tables |

I checked the assumption behind skipping documents: none of the kernel scripts reads a `.md`, `.tex`, `.pdf` or `.bib` file as input (`progress.md` is an output), and the contract pins no file of those types.

## Notes

- **This PR edits `KERNEL_CONTRACT.json`**, re-pinning the kernel workflow and `.gitattributes` and adding the two new scripts. That is required by the contract's own design, since it pins the workflow. It is Jack McCarthy's file; Astra has asked him to confirm the input list. I see no reason the merge must wait for that, since the rule errs toward building, but the owner may prefer to.
- **The skip script exists twice**: embedded in the workflow and as `scripts/kernel_pr_scope.py`. The tests should keep them identical; a future edit must change both.
- **A pull request can still change the workflow that checks it.** That is true of every `pull_request` check here and is not new. Changes under `.github/` are classed as "new result or route" by the review gate.
- **This PR itself gets the full build**, because it changes kernel inputs.

## Live test status, for the record

Run 43527659588 on PR 69, on `main` at `81ecf0b5`, completed with success in about a minute and a half. Both reviewers finished and accepted, each API returned the exact requested model ID, and the App's check moved from blocked to passing. Still untested: an intentional error and its repair, a changed head, an interruption, both override cases, a forged check, a branch workflow trying to read the secrets, and a real `pause_turn`.
