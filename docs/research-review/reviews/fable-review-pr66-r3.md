# Third review of draft PR 66: Protocol B gate

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.
Reviewed: commit `298691f6` on `codex/protocol-b-gate`, against my second review of `c330efa1`.

**Decision: accepted for merge as an inactive workflow.** This is acceptance of the implementation as read and tested offline. It is not acceptance of the gate's live behaviour, which the throwaway-PR test must establish before activation.

**Independence.** Independent of the code, not of the design.

## What I checked

- Read the full diff from `c330efa1` to `298691f6`.
- Ran the 38 committed tests: all pass, standard library only, no network.
- Re-ran my own probe on the new script.
- Confirmed the r3 review packet's workflow, instructions, tests, setup checklist and `PROJECT.md` are identical to the PR head.

## Status of the second review's points

| Point | Status |
|---|---|
| N1. Long working prose aborted the review | **Fixed.** Full notes go to the run artifact; the comment keeps recent notes with a notice and link. My probe ran 50 turns of about 5,000 characters each without the notes stopping it. |
| N2. Editorial rule named files that do not exist | **Fixed.** The rule now lists `README.md` and `CREDITS.md`. A credits edit with the declaration is classed as editorial in my probe. |
| N3. Earlier findings are read from bot comments | **Documented** as a limit in the setup checklist: collaborators with write access are trusted to preserve that history. Not changed in code. Acceptable. |
| N4. Tool-result budget exceeds the context window | **Documented** in the setup checklist. Not changed in code. Acceptable. |

## Unchanged from the second review: the live test must cover

- The whole OpenAI request, and whether its API returns exactly `gpt-6-astra` as the model ID.
- That GitHub accepts changing a completed `action_required` check to `success`, and that the ruleset treats it as passing.
- That the Environment's branch restriction admits `pull_request_target` runs for a fork PR and refuses a workflow on a branch.
- A no-argument `read_history` call and a real `pause_turn` on the Anthropic API.
- Whether a full review fits in the 120-minute job limit, and what a run costs.
