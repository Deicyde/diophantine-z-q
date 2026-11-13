# Response to Fable's PR66 review

Implementation response, November 13, 2026. This records author repairs, not
independent acceptance of those repairs. The gate remains inactive.

The [original review](pr66-fable.md) requested changes to `efb971cf`. The owner
selected the dedicated App option. No live model calls or setting changes were
made while implementing this response.

| Finding | Repair and validation |
|---|---|
| 1. Check spoofing and secret access | A dedicated App writes the check; the job uses the default-branch-only `protocol-b` Environment. Official pinned token actions create separate start/finalization tokens. The workflow token cannot write checks. Live auto-merge requires the exact App integration ID. Offline tests reject a same-name Actions check. Environment creation and live verification remain pending. |
| 2. Override depended on model agreement | Code applies authenticated exact-head overrides to the latest pair of completed App-stored reports, without model calls. Every new or unresolved finding needs coverage. Summaries print full IDs and the not-outside-reviewed qualification. Tests cover uncovered, stale and incomplete reports and a covered deadlock. |
| 3. Comment flood and repeated history | Working prose updates one comment per reviewer/run. Completed own reports and working notes are excluded from repeated discussion; all structured findings persist separately. Interrupted observations remain available. Tests include over one million characters of old reports and comment updates. |
| 4. Anthropic stream handling | Empty JSON deltas parse as `{}`; `pause_turn` resumes the unchanged assistant content without a new user message. Both output limits are 64,000 tokens. Refusal and output-limit errors identify the stop reason and details. All have stream fixtures. |
| 5. Cache use | Anthropic automatic prompt caching is enabled. File text and split lines are cached in memory by path/revision. Tests verify one fetch for multiple page reads. |
| 6. Transient provider errors | At most two retries of initial 429/5xx responses, before receiving a stream. No automatic retry of GitHub writes or partial streams. An infrastructure error does not become a permanent invented mathematical finding. |
| 7. Unrelated changes on main | Compare the workflow and instructions, not just the main commit ID. An unrelated main advance no longer discards the review. The strict up-to-date branch rule remains. Reuse across different PR head commits is not implemented; reviewers reuse unchanged mathematical units within the new run. |
| 8. Editorial scope | Extend the path/diff rule to ordinary README, credits and navigation corrections with the author's no-mathematical-change declaration; math and policy indicators escalate. Tests cover ordinary typos, credits, incomplete diffs and mathematical changes. |
| 9. Missing tests | `tests/protocol_b/test_gate.py` loads the actual embedded workflow program and runs with Python's standard library. No API keys are needed. |
| 10. Outside-review description | Acceptance states that, when either family authored the change, only the other is an outside reviewer. Overrides retain the explicit qualification. |

Smaller points are also addressed. A new check starts in completed
`action_required` state, so a canceled/lost job leaves it blocked. Comment
triggers prefilter command shape and collaborator association, followed by a
current-access API check. `PROJECT.md` now lists load-bearing steps with current
manuscript labels. The instructions explain paywalled-source handling.

The App stores compact decisions in its own check output because ordinary
GitHub Actions comments are forgeable by another workflow. Comments still hold
the readable reports and prior objections, but cannot authorize an override.
This uses the same workflow and GitHub API, without a controller or custom
signing service.

Offline validation passes 36 regression tests. A separate full-size simulation
reads the current 2,338,864-byte, 45,035-line TeX through both source-tool paths
and completes the review/publication stages with fake providers and fake GitHub
writes. That test does not establish live API compatibility, model context
capacity, mathematical correctness or actual App/Environment enforcement.

Before activation: Fable reviews these changes, the owner configures the new
App and Environment, and a throwaway PR exercises real APIs, interruption,
overrides, exact-head checks and protected merging. See the
[setup checklist](../protocol-b-setup.md). Until then, no required check or
auto-merge setting is changed.
