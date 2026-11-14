# Pre-activation implementation reviews

Recorded November 13, 2026 (America/Los_Angeles), during PR87's documentation
repair. The implementation requirement remains independent review by a model
outside the author's family. Activation does not delete that requirement or
extend an earlier review to later code.

Elliot Glazer supplied the seven reviewer-authored files linked below. They are
committed unchanged. PR73's file was written retrospectively from the session
record, as its header states; it is not a new review. Later in-session acceptances
reported by Elliot are distinguished from the commits covered by a file. An
operator's account of an acceptance is not a substitute reviewer report.

| Change and review round | Preserved evidence and scope | Outcome and limits |
|---|---|---|
| [PR66](https://github.com/elliotglazer/diophantine-z-q/pull/66), round 1 | [Original Fable 5.2 report](fable-review-pr66.md), reviewing `efb971cf`; [implementation response](pr66-response.md). | Changes requested. Preserve the original objections and their scope. |
| PR66, round 2 | [Original Fable 5.2 report](fable-review-pr66-r2.md), reviewing `c330efa1`; [implementation response](pr66-response-r2.md). | Earlier repairs accepted; new findings required further repairs. This report does not certify later commits. |
| PR66, round 3 | [Original Fable 5.2 report](fable-review-pr66-r3.md), reviewing `298691f6`. | Accepted for merge **as an inactive workflow**, after 38 offline tests and probes. It explicitly leaves live behavior to the throwaway-PR tests. |
| [PR71](https://github.com/elliotglazer/diophantine-z-q/pull/71) | [Original report](fable-review-pr71.md) on `5c98b2ab`: cache/retry changes accepted, **changes requested** on context-budget aborts. | Elliot reports that the later missing-file tool-result fix and Actions job rename were accepted in session. Those later changes are not covered by this file. The budget finding remained and was addressed in PR72. Final PR head: `e423ca77e784bb4c2de95ed23e38d9965b906513`. |
| [PR72](https://github.com/elliotglazer/diophantine-z-q/pull/72) | [Original report](fable-review-pr72.md) accepts `73f4dc78`, with budget probes and kernel-scope tests. | Acceptance of later commits was given to Elliot in session, according to his report. The file's coverage remains `73f4dc78`; final PR head was `2e97e3105bb224768351c4e3643c711d47b2db42`. |
| [PR73](https://github.com/elliotglazer/diophantine-z-q/pull/73) | [Fable's retrospective record](fable-review-pr73.md) of the review given in conversation: initial review on `8e37c7d6`, low-disk repair on `a15b23e6`, and resolved merge on `c8ce014f`. [Repair record](https://github.com/elliotglazer/diophantine-z-q/pull/73#issuecomment-6868835819); [hosted measurements](https://github.com/elliotglazer/diophantine-z-q/pull/73#issuecomment-6869166436). | Accepted in session, recorded afterwards from that session; no new review was performed for the file. It distinguishes Fable's source checks from Astra's reported hosted memory measurements. Later commits not covered by the record have only the in-session acceptance reported by Elliot. |
| [PR88](https://github.com/elliotglazer/diophantine-z-q/pull/88) | [Original report with follow-up](fable-review-pr88.md) accepts `41dd936f` after offline probes and 54 tests, accepts documentation commit `268c4129`, and identifies the null-caller hardening. [Published Astra report](https://github.com/elliotglazer/diophantine-z-q/pull/88#issuecomment-6870172880) requested the documentation correction. | The null-caller repair was committed as `152654f94d48aedfbe79b3382b74759c06ca866a`; the file recommends that repair but is not a separate acceptance report on that commit. Elliot reports the final merge was by **owner bypass on Fable's review and the Astra reviewer's report, not on an App acceptance**. The report explicitly records that exceptional merge path. |

PR88 merged at `2026-11-14T02:40:22Z` (November 13, 18:40 PST), producing
`f5cccda2468597b693e2f4eb0b58085e5bd89f9b`. Its bypass does not demonstrate the
protected auto-merge path. No App approval is inferred from that merge, and no
later author commit is treated as covered merely because an earlier report
accepted a related change.

## Activation limits

The owner authorized activation and the scoped initial live tests. The
[test evidence and settings readback](activation-2026-11-13/README.md) record
what was observed, by whom, and when. A branch/tag secret-access denial test
and a successful protected live merge were not completed at this snapshot.
The interruption, unauthorized-override and real `pause_turn` tests were
expressly deferred. The implementation has original and owner-reported
outside-family reviews as distinguished above; this index does not claim a
preserved, independently verifiable final report for every repair.

This review history covers the gate and its CI support. It does not establish
the manuscript's mathematics, confer new acceptance on historical proofs, or
waive the requirement to review future changes.
