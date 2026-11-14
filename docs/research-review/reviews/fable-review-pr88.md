# Review of PR 88: Fable server-tool context accounting and web caps

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.
Reviewed: commit `41dd936f` on PR 88 (2 files: the gate workflow and its tests), against `main` at `9405798b`.

**Decision: accepted for merge.**

**Independence.** Independent of the code. My first diagnosis of the PR 87 failure (web payloads counted by size) was one of two causes; Astra found the other (cumulative usage) from the run artifact.

## What I checked

- Read the full workflow diff.
- Ran the 54 committed tests: all pass, no network.
- Reproduced the PR 87 failure offline. I simulated a Fable turn that fetches a 1 MB web page, with a modest context reported at the start of the request and cumulative cached input reported at the end, as the real API did.

| Gate version | Result |
|---|---|
| `main` (`9405798b`) | Review aborted: "estimated 2,652,542 including reserves; limit 400,000" |
| PR 88 (`41dd936f`) | Review completed and accepted in two model requests |

- Confirmed the web result block is still replayed to the provider unchanged, which the API requires.
- Re-ran my earlier probes on PR 88: oversized repository reads are still refused with a warning, and the stream handling is unchanged.

## What the fix does

1. **Reads the right usage figure.** The context estimate now uses the input reported at the start of the request, not the end-of-request total that adds the same cached input once per internal server-tool call. If that figure is missing and server tools were used, it falls back to the previous estimate.
2. **Stops counting web payloads by size.** For web search and web fetch result blocks, bytes beyond a fixed reserve are excluded from the estimate. The next request's reported input corrects any error.
3. **Caps the web tools on the request:** 3 searches and 5 fetches, with fetched text limited to 20,000 tokens each.
4. **Tells the reviewer** how many web uses remain and that fetched text may be truncated.

## For the owner to know

- **Fable's reviewer now has a small web allowance.** Three searches and five fetches per turn, 20,000 tokens of text per fetch. Astra's reviewer has no such cap; on PR 87 it consulted well over a dozen pages. For a mathematical PR that changes how a published theorem is applied, five fetches may not be enough to check primary sources, and the reviewer is instructed to request changes when it cannot. Expect some of those. The caps are constants and can be raised once real reviews show what is needed.
- **Two of the reserves are assumptions, not limits.** Search results and binary documents such as PDFs are not covered by the fetch cap. A very large PDF could make one request bigger than estimated; the following request's reported input would correct it, and the guard would stop the review then if needed.
- **This PR has to pass the gate that is on `main` now**, which still has the bug. If Fable's reviewer uses web tools while reviewing it, the review will abort the same way.

## Follow-up review of commit `268c4129`

**Decision: the documentation change is accepted. One small hardening is recommended before merge.**

- The live gate ran on PR 88 using the workflow on `main`. Fable's reviewer aborted with the known context-estimate bug (estimated 1,156,423), so the run is not an App acceptance. Astra's reviewer completed and raised one finding, `DOC1`: the setup guide still described the old estimator. That was a fair finding, and my first review did not check the guide.
- Commit `268c4129` changes only `docs/research-review/protocol-b-setup.md`. The workflow and tests are byte-identical to the commit I reviewed. I checked the new text against the code: the three reserves (20,000, 16,000, 128,000), the caps (3 searches, 5 fetches), the use of the request-start usage figure, the fallback, the recalibration, and the allowance fields on every tool result are all described accurately, and the text says plainly that the reserves are assumptions and the guard enforces an estimate.
- **Recommended hardening.** Astra's reviewer noted, then withdrew as unproven, that a web call whose `caller` field is `null` would crash `web_allowance`. I confirmed the crash offline: `block.get('caller', {}).get(...)` raises `AttributeError` when the field is present and null, and that would abort the Fable review. Whether the API ever sends null is not established. The fix is one line, `(block.get('caller') or {})`, plus a test. It is worth doing now, because an abort here would block the repository again.

## Merge path

The gate on `main` cannot pass this PR, because the bug it fixes stops Fable's reviewer whenever it uses web tools. The owner merges it by temporarily removing the App check from the ruleset. This merge therefore rests on this review and on Astra's reviewer report, not on an App acceptance, and should be recorded as such on the PR.

## Not verified

- Live behaviour: that the API accepts `max_uses` and `max_content_tokens` as sent, and that the start-of-request usage is reported as the code expects. The live run on this PR or the re-run of PR 87 will show both.
