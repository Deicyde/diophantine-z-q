# Second review of draft PR 66: Protocol B gate with dedicated App

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.
Reviewed: commit `c330efa1` on `codex/protocol-b-gate` (8 files), against my first review of `efb971cf`.

**Decision: the repairs to all ten findings are accepted. Two small new defects should be fixed in this PR before it is merged. After that it can be merged inactive and taken to the live test.**

**Independence.** Unchanged from the first review: independent of the code, not of the design.

**How I reviewed.** I read Astra's response, the full workflow diff, the setup checklist, and the changes to the reviewer instructions, `PROJECT.md` and the contributor guide. I ran the 36 committed tests (all pass, standard library only, no network) and re-ran my own probe against the new script. I checked the pinned token action against GitHub. Nothing was run against either model API or against this repository's settings.

## Findings from the first review

| # | Finding | Status |
|---|---|---|
| 1 | Check could be forged; keys readable from branches | **Repaired.** The check is created and finalized with a token for the dedicated App; the job uses the `protocol-b` Environment; the workflow's own token has `checks: read`; live mode refuses to request auto-merge unless the ruleset pins `Protocol B / review` to the App's integration ID. The pinned action `fee1f7d6…` is `actions/create-github-app-token` v2.2.2 and accepts `permission-checks`. |
| 2 | Override needed the objecting model's consent | **Repaired.** An override command makes no model call. It reads the latest completed pair of reports from the App's own check output, requires both to be complete, current and from the right models, and passes only if every new or unresolved finding is covered. Full finding IDs are printed in the summary. |
| 3 | Comment flood and the one-million-character limit | **Repaired**, with one new defect (N1 below). One working comment per reviewer per run; the gate's own notes and reports are excluded from the discussion fed back to reviewers; the size limit is gone. |
| 4 | Anthropic stream handling | **Repaired.** My probe now parses a no-argument tool call in all three shapes. A paused turn is resumed with no added user message. Both output limits are 64,000. Refusal and output-limit stops are reported as such. |
| 5 | No prompt caching; repeated downloads | **Repaired.** Top-level `cache_control` is set; file lines are cached per path and revision. |
| 6 | No retry on transient errors | **Repaired.** Up to two retries of an initial 429 or 5xx from a model provider, before any stream is received. An infrastructure failure no longer creates a finding. |
| 7 | Run discarded when `main` moves | **Repaired as far as stated.** The run now compares the workflow and instruction files, not the branch tip. Reusing an accepted review across PR head commits is not implemented, and the response says so. |
| 8 | Editorial class too narrow | **Repaired in design**, with one new defect (N2 below). |
| 9 | Tests not in the PR | **Repaired.** 36 tests are committed and pass. |
| 10 | Outside-review wording | **Repaired.** |

## New defects to fix before merge

### N1. A reviewer that writes a lot of working prose is aborted

When the accumulated working notes exceed 45,000 bytes, the code raises an error from inside the review loop. That ends the review as a failure. In my probe, ten turns of about 5,000 characters of prose each aborted the review. The error message says the full text is preserved in the artifact, which is the right behaviour, but the review should continue.

Fix: when the comment would be too large, post the most recent notes with a line saying earlier notes are in the run artifact. Do not raise.

### N2. The editorial rule names files this repository does not have

The rule lists `README.md`, `CONTRIBUTORS.md`, `docs/credits.md` and `docs/navigation.md`. Only `README.md` exists. The credits file here is `CREDITS.md` at the root, so a credits edit still goes to both models. Use the real paths, and update the setup checklist's wording to match.

## Should fix or document

### N3. The history of earlier findings still comes from bot comments

Override authority now comes from the App's check, which is right. But the list of earlier findings that reviewers must disposition is still parsed from comments posted by `github-actions[bot]`. A workflow run by someone with write access posts as the same bot and could edit or delete those comments, which would drop earlier findings from later runs. Outside contributors cannot do this from a fork. Either build the earlier-findings list from the App's check outputs across the PR's commits, or state this limit in the setup checklist.

### N4. The context budget is still larger than the model's context window

The 8,000,000-character limit on tool results is unchanged. A review that reads that much will hit the provider's context limit first and fail as an infrastructure error. Lowering the budget to something that fits would give a clearer message.

## For the owner

- The checklist says to create a new App. Reusing "Elliot Research Review Gate" with a new key and the old keys deleted meets the same goal. Check under **Install App** that it is installed only on `diophantine-z-q`.
- Names the workflow reads, all in the `protocol-b` Environment unless noted:
  - Secret `PROTOCOL_B_APP_PRIVATE_KEY`: the contents of the `.pem` file.
  - Secret `OPENAI_API_KEY`.
  - Secret `ANTHROPIC_API_KEY`.
  - Variable `PROTOCOL_B_APP_ID`: `5663093`.
  - **Repository** variables `PROTOCOL_B_MODE` and `PROTOCOL_B_TEST_PR`. These must be repository-level, because the job's start condition is evaluated before the Environment is loaded.

## Still unverified; the live test must cover these

- The whole OpenAI request, and whether its API returns exactly `gpt-6-astra` as the model ID.
- That GitHub accepts changing a completed `action_required` check to `success`, and that the ruleset then treats it as passing.
- That the Environment's branch restriction admits `pull_request_target` runs for a fork PR and refuses a workflow on a branch.
- A no-argument `read_history` call and a real `pause_turn` on the Anthropic API.
- Whether a full review fits in the 120-minute job limit.

## Smaller points

- The token action is pinned to v2.2.2; the current major version is 3. Not a defect, but worth updating before long.
- Each run under an Environment records a deployment, which will show in the PR timeline.
- Any edit containing a digit or a common mathematical word is escalated out of the editorial class. That is conservative and acceptable.
- The load-bearing list in `PROJECT.md` was written by the author's model family. It is a reasonable map, and the instructions correctly let a reviewer add to it.
