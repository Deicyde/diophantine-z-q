# Review of draft PR 66: inactive Protocol B review gate

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.
Reviewed: commit `efb971cf` on `codex/protocol-b-gate` (`.github/workflows/protocol-b.yml`, `.github/protocol-b-reviewer.md`, `PROJECT.md`).

**Decision: changes requested.** The design is sound and fails closed almost everywhere, but four problems should be fixed before the live test, and one of them undermines what the check is supposed to prove.

**Independence.** I did not write this implementation. I did design Protocol B and write the instructions Astra implemented from, so I am independent of the code and not of the design.

**How I reviewed.** I read all three files in full, ran the embedded script against simulated provider streams and inputs (no network, no API calls), and checked two Anthropic API details against the live documentation. I did not see the 22 tests or the review packet, and I did not run anything against GitHub or either model API.

## What is right

- No checkout, no dependency install, and no candidate code is executed. The script is embedded in the default-branch workflow and reads the PR only through the API.
- No untrusted value is interpolated into the shell; the heredoc is quoted.
- Reviewer instructions are loaded from the default branch at a pinned commit.
- Failure is closed: an incomplete stream, a missing report field, an undispositioned earlier finding, a truncated tree or diff, a changed head, or a model ID that differs from the one requested all block.
- Earlier findings persist across runs and each must be dispositioned.
- Auto-merge is requested only after checking that the reviewer check and the 14 computation checks are required and that the branch must be up to date.
- Inactive unless a repository variable is set; test mode is limited to one designated PR.
- The reviewer instructions are faithful to Protocol B: PR content is data, three claim states, the published-theorem boundary, closure at the point of use, and what an override does and does not mean.
- `web_search_20260318` is a current tool version (confirmed in the live documentation). I did not check `web_fetch_20260318`.

## Must fix before the live test

### 1. The required check can be satisfied by a workflow in the pull request

GitHub matches a required status check by its name and the app that posted it. Every GitHub Actions job posts as the same app. So a pull request that adds a workflow with a job named `Protocol B / review` that simply exits successfully produces a passing check with the required name on its own head commit. The same token-based mechanism means any collaborator who pushes a branch containing a workflow can read both API keys and post any check result.

The gate itself would still fail or request changes, and it enables auto-merge only on its own success. But a collaborator looking at the PR would see a green `Protocol B / review` and a working merge button. The same applies to the 14 computation checks, since `pull_request` workflows run the PR's version of the workflow files; the reviewers are told to inspect workflow changes, which helps only if the real review is what gates the merge.

Options:
- **Robust:** post the check from a dedicated GitHub App identity used only for this purpose, pin the ruleset's required check to that App, and keep its key and the two model keys in a GitHub Environment restricted to the default branch. This is an identity, not a service; there is no controller.
- **Minimum:** move the three secrets into a default-branch-only Environment, require approval for all outside contributors' workflow runs, and document that collaborators with write access are trusted not to forge the check.

**Owner's decision (November 13): the dedicated App identity.** Implementation notes:

- Add `environment: protocol-b` to the job. The owner will create that Environment, restrict it to the default branch, and put the App's private key and the two model API keys in it as environment secrets, with the App ID as an environment variable. Repository-level secrets are not used.
- Mint the App's installation token with the official `actions/create-github-app-token` action, pinned to a commit SHA. Python's standard library cannot sign the App JWT, and nothing should be installed.
- Create and complete the `Protocol B / review` check run with the App token. Keep the workflow's own token for reading the PR, posting comments and requesting auto-merge.
- Before requesting auto-merge, verify that the ruleset pins `Protocol B / review` to this App's integration ID, not to GitHub Actions.
- State in the contributor guide that only a check from this App counts, and that a workflow job with the same name does not.

### 2. A collaborator's override only works if the objecting model agrees

An override comment triggers a full re-review by both models, and the check passes only if the reviewer that raised the finding chooses to mark it `overridden`. A model that still believes the step is wrong can answer `unresolved`, and the deadlock continues. Protocol B says the collaborator decides.

Fix: apply overrides in code. On an override command, evaluate the latest reports for that head: if every unresolved and new finding is covered by an authenticated override, pass with the "not outside reviewed" note, without calling either model.

Also print each finding's full ID (`run-attempt-reviewer-id`) in the check summary. A collaborator currently has to assemble it by hand from the JSON comment.

### 3. The gate's own comments will eventually break it, and will flood the PR

- Every model turn that contains prose is posted as a PR comment. With up to 50 turns per reviewer, one run can post dozens of comments, each of which notifies subscribers.
- `history()` feeds all issue comments back to the reviewers, including the gate's own working notes and JSON reports, and raises an error when the discussion exceeds 1,000,000 characters. After a few runs on one PR that limit is reached and the gate can never pass on that PR again.

Fix: exclude the gate's own working notes and report comments from `discussion` (the reports are already carried in `earlier_findings`), and keep working notes in the run artifact or in one comment that is updated.

### 4. Anthropic stream handling

Results from the simulated-stream probe:

| Case | Result |
|---|---|
| Tool call with arguments | Parsed correctly |
| No-argument tool, deltas `""` then `"{}"` | Parsed correctly |
| No-argument tool, only the empty first delta | **Crash: `json.loads("")`** |
| `stop_reason: refusal` | Blocked, reported as "incomplete or output limit reached" |
| `stop_reason: max_tokens` | Blocked, same message |

- **Empty tool input.** The documented stream begins every tool call with an empty `partial_json`. `read_history` takes no arguments and must be called before finishing, so if the API sends only that empty delta for it, every Fable review fails. Use `json.loads(partial or "{}")`. I could not confirm from the documentation which shape the API sends for a no-argument tool, so the live test should exercise it either way.
- **`pause_turn`.** When there are no client tool calls the loop appends a user message telling the model to continue. For a paused server-tool turn the documentation says to send the assistant message back unchanged and add nothing. Resume without the extra message when `stop_reason` is `pause_turn`.
- **Output limit.** `max_tokens` is 16,384. On Fable 5.2 thinking is always on and counts against that limit, and the final report can be up to 45,000 bytes. Hitting the limit blocks the review. Raise it to about 64,000; the request already streams. The same concern applies to `max_output_tokens` on the OpenAI request.
- **Refusal.** Report `stop_reason` and `stop_details` as such, so a refusal is not misread as a transport fault.

## Should fix

5. **No prompt caching on the Anthropic request.** The whole conversation is resent on each of up to 50 turns at the full input price. Add top-level `"cache_control": {"type": "ephemeral"}`. Also cache file contents in memory: each 1,000-line read currently downloads the entire 2.3 MB manuscript again. The 8,000,000-character budget is larger than the model's context window, so the context limit will be hit first.
6. **No retry on transient provider errors.** A single 429 or 5xx becomes a persistent `interrupted_review` finding that both reviewers must disposition in every later run. Add a small bounded retry with backoff before any output has been produced.
7. **A run is discarded if `main` moves while it is in progress**, and the up-to-date rule means each merge forces a complete re-review of every other open PR, because acceptance is tied to the head commit. Protocol B says a review stays valid until the unit, its dependencies or its consumers change. At minimum, compare the instructions file and workflow at the end instead of the branch tip. Reusing an accepted review when only the base moved is a larger design choice for the owner.
8. **The editorial class is far narrower than the protocol.** Only trailing-whitespace changes to Markdown skip review; a README typo or a credits line gets two full model reviews. Either widen the rule by path, or change the protocol text to match.
9. **The tests are not in the PR.** Commit them, so the gate's logic can be re-run by anyone, and add the empty-delta case.
10. **Reporting.** The success summary says "both approved reviewers accepted". It should add that when one of those families authored the change, only the other is an outside review.

## Not verified

- Everything on the OpenAI side: the request fields, and whether the API echoes exactly `gpt-6-astra` or a dated snapshot ID. If it echoes a different string, every run fails on the model check. The live test must cover this.
- Live behaviour of either API, GitHub's auto-merge mutation, and timing against the 120-minute job limit.
- `web_fetch_20260318`.

## Smaller points

- A cancelled or timed-out job leaves the check in progress.
- Any comment beginning `/protocol-b ` starts a runner before the permission check.
- Protocol B asks for a list of load-bearing steps; `PROJECT.md` does not have one yet.
- Sources behind paywalls will block reviews of changed theorem applications. Decide how those are handled before the first such PR.
