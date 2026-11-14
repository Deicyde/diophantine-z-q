# Review of PR 71: review cache lifetime and context budget

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.
Reviewed: commit `5c98b2ab` on `codex/protocol-b-review-budget` (4 files), against `main` at `68197d94`.

**Decision: changes requested, one item. The cache and retry changes are right. The context budget does what it says, but it ends a review where it should tell the reviewer to read less.**

**Independence.** Independent of the code. I suggested the three precautions this PR implements, so I am not independent of the approach.

**How I reviewed.** Read the full diff, ran the 43 committed tests (all pass, no network), and ran my own probe of the budget with simulated manuscript-sized reads. No model API was called.

## Accepted

- **One-hour cache.** `"cache_control": {"type": "ephemeral", "ttl": "1h"}` is the documented form. The setup checklist states the cost correctly: cache writes at twice the base input price.
- **Rate-limit retries.** Waits of at least 65 then 130 seconds on a 429, honouring a longer `Retry-After` up to five minutes and stopping if the provider asks for more. Other server errors keep the short backoff. Sensible for a per-minute limit.
- **Budget accounting.** After the first response the estimate uses the provider's reported input tokens, including cache reads and writes on the Anthropic side, so it does not drift. Counting only the newest material by bytes is conservative by design.
- **Not adding a token-counting request.** Correct, since that endpoint does not accept the server tools the gate uses.

## Change requested

### 1. Going over budget aborts the review; the reviewer is never told

`context_budget` raises before the next model request, which ends the review as an infrastructure failure. New material is counted in bytes as if each byte were a token, so a few large reads in one turn trip it even when the real token count is modest. The reviewer gets no warning and no chance to narrow its reads, and a rerun will likely do the same thing.

Probe results, simulating reads of an 80-byte-per-line file the size of the current manuscript and a provider reporting 0.3 tokens per byte:

| Reading pattern | Result |
|---|---|
| One 1,000-line read per turn | Stopped before turn 11, after about 10,000 lines |
| Two 1,000-line reads per turn | Stopped before turn 5, after about 8,000 lines |
| Four 1,000-line reads per turn | Stopped before turn 2, after the first 4,000 lines |
| Six 1,000-line reads in the first turn | Stopped before turn 2 |

Models commonly issue several reads in parallel, so the last two rows are realistic.

Fix: enforce the budget where the reviewer can respond to it.

- In `read_file`, `list_files` and `read_history`, if returning the result would take the next request over budget, return a tool error that says so and gives the remaining allowance, and let the review continue.
- Include the remaining allowance in every tool result, so the reviewer can plan.
- Keep the existing pre-request check as the last line of defence.

This is the same class of defect the first live run found: a recoverable condition during a tool call ends the review. It makes sense to fix both in one change.

## For the owner to know

- **A reviewer can read about a fifth of the manuscript in one review.** With a 400,000-token budget, the probe's reviewer got through roughly 10,000 of 45,035 lines. That is fine for reviewing a change and its consumers. It means a whole-manuscript audit cannot be done through this gate in a single run.
- **The 400,000 figure follows from your current Anthropic rate limit** of 500,000 input tokens per minute: a request larger than that could not be sent at all after a cache miss. If the limit is raised, the budget can be too. It is a constant in the workflow, so changing it needs a PR.
- **A very large PR cannot start.** Before the first response the estimate is the size of the whole request in bytes, which includes the PR's file list and diffs. A PR whose file list and patches exceed about 330 KB is stopped before any review. PR 65's was 75 KB.

## Not verified

- The exact shape of Anthropic's spending-cap error that the code looks for (`error.details.error_code`). If the shape is different the only effect is two wasted retries.
- Any live behaviour: real token counts per byte for this manuscript, cache hit rates, and how often a 429 occurs.

## Ordering

This PR and the fix for the live-test failure (a file missing at `base`) both change the workflow. Whichever merges second will need rebasing, and the in-progress test on PR 69 must be re-run after each merge, since a change to the workflow or instructions invalidates a run in flight.
