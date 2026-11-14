# Protocol B setup and test checklist

Status: the owner activated Protocol B for future pull requests on November 13,
2026, America/Los_Angeles. Astra's authenticated readback at 18:57 PST that day
(November 14, 02:57 UTC) observed live mode and the App-pinned requirement.
See the [settings evidence and limits](reviews/activation-2026-11-13/README.md)
and [pre-activation review record](reviews/pre-activation-reviews.md). This is
operator-reported deployment evidence, not a claim that every setup or test
below has been independently demonstrated. The old controller stays retired.

## Identity and credentials

The owner creates a dedicated GitHub App for this gate. Give it only repository
Checks read/write, plus GitHub's mandatory metadata read access, and install it
only on `elliotglazer/diophantine-z-q`. It needs no webhook, code-write permission,
or external server. The retired App identity can instead be reused after
rotating its key, deleting its old keys, removing any other installations and
confirming the old controller cannot use the new key. Do not reuse the retired
controller's key. These setup operations require the owner's authorization.
The dated readback records the App ID and Environment branch restriction; it
does not establish key rotation, other installations, or absence of key copies.

Create a GitHub Environment named `protocol-b`. Restrict its deployment branches
to the default branch, `main`. Do not permit arbitrary branches or tags. Put:

| Type | Name | Value |
|---|---|---|
| Environment variable | `PROTOCOL_B_APP_ID` | The dedicated App's numeric App ID, also its integration ID |
| Environment secret | `PROTOCOL_B_APP_PRIVATE_KEY` | The dedicated App's fresh private key |
| Environment secret | `OPENAI_API_KEY` | Key allowed to call `gpt-6-astra` |
| Environment secret | `ANTHROPIC_API_KEY` | Key allowed to call `claude-fable-5-2` |

Do not put these keys in repository-level secrets. Branch workflows must not be
able to access them. Keep values out of comments, logs and review packets.

`PROTOCOL_B_MODE` and `PROTOCOL_B_TEST_PR` are **repository variables**, not
Environment variables. The job's start condition needs them before GitHub loads
the Environment. They are settings, not secrets.

The workflow uses the official, commit-pinned `actions/create-github-app-token`
action twice. One token creates the initially blocked check; a fresh token
finalizes it after the potentially long model review. The action revokes its
tokens at job cleanup. The ordinary workflow token reads sources, posts comments
and requests protected merges and post-merge workflow dispatches. Only the App
token writes the review check.
The Actions job is named `Run reviewers and publish App check`. It is distinct
from the App-issued `Protocol B / review` check, or `Protocol B / test review`
in test mode. A green Actions job alone is not App acceptance.

## Review behavior

The job runs trusted default-branch code and instructions. It never checks out
or executes the candidate PR. Both approved models receive pinned source reads
and web tools. Reports record actual returned model IDs, source reads and usage.
There is no fallback model. Unavailable sources, unfinished reviews and changed
heads do not pass.

Automatic reviews run only for PR authors whose current GitHub permission is
write, maintain, or admin. Other authors get an App check saying "awaiting a
collaborator's /protocol-b review". A current collaborator must post that exact
command to start each review; a manual workflow dispatch is not a substitute
for an outside author's PR. Permissions are checked through GitHub's API.

Before review, and again before each model request, the gate reads required
computation checks. A concluded failure blocks further model calls with "fix
failing checks first". Pending checks can run in parallel with review. A PR
gets at most four automatic rounds; further rounds require the collaborator
command. Started automatic rounds count even if interrupted. Each start is
saved in the App check, with a pointer on the PR so force-pushing does not lose
the count. Earlier report records locate historical checks; only verified App
records authorize reuse or contribute to the count. Check output records the
number of automatic rounds. A completed review on the same head under identical
workflow and instruction files is reused for automatic events, including
reopen, ready-for-review, and duplicate synchronization events.

A `read_file` lookup returning HTTP 404 produces a tool result identifying the
missing path and pinned revision. For example, a newly added file may be absent
at `base` but readable at `head`. The model can correct the request and continue.
The failed lookup does not count as a source read. Permission errors, server
failures and a missing blob after a successful file lookup still stop the run.

The initially completed `action_required` check says that review has not been
accepted. Finalization replaces that result. Cancellation or a lost runner
therefore leaves a blocked check rather than an indefinitely running one.

A complete diff and the exact declaration `No mathematical content changed.`
permit the editorial path. It accepts trailing-whitespace-only Markdown changes
outside policy paths and text-only corrections in the actual root files
`README.md` and `CREDITS.md` when no mathematical or policy terms
trigger escalation. Other changes receive both reviews. This is a conservative
classification rule, not a proof that arbitrary natural language is harmless.
Do not use the declaration to misclassify a change.

Working notes update one comment per reviewer/run. If they exceed the comment
limit, the comment shows recent notes and links to the run artifact containing
the complete notes. The review continues. After an interrupted run, retrieve
any omitted observations from that artifact; an unavailable artifact leaves
that part of the history unchecked. Completed reports are appended, and their
findings are supplied to later reviews. HTTP failures are logged. Except for the
missing-file case above, they remain infrastructure failures rather than
invented mathematical objections. Initial 429
and 5xx responses from a model provider get at most two retries. Rate-limit
retries wait at least 65 then 130 seconds, and respect a longer `Retry-After`
up to five minutes. A longer requested wait stops the run rather than retrying
early. Short backoff remains for other transient server failures. A recognized
Anthropic spending-cap error is not retried. Partly received
streams and uncertain GitHub writes are never automatically replayed.

A new default-branch commit does not invalidate an in-flight review if the
trusted workflow and instructions are unchanged. GitHub must still require the
PR branch to be up to date before merging. A new PR head needs a fresh run;
reviewers reuse unchanged mathematical arguments within their review scope.

### Documented limits

Earlier findings are read from `github-actions[bot]` comments. A collaborator
with write access can run a workflow as that bot and edit or delete its
comments. The gate therefore trusts collaborators to preserve review history;
it does not reconstruct tamper-resistant history from App checks across all PR
commits. Outside fork contributors do not have that ability. This limit does
not change override authority, which still comes from the dedicated App's
check output rather than bot comments. Preserve substantive objections in the
project's findings record as well as the PR discussion.

Both reviewers default to a preflight context budget of 400,000 estimated tokens.
The repository variable `PROTOCOL_B_MANUSCRIPT_PROFILE` defaults to `standard`
when unset or empty. An owner can set it to `expanded` when the provider accounts
allow the larger spending profile. Only then, if the complete GitHub diff changes
a path under `manuscripts/`, including a rename out of that directory, both
receive 900,000. Other PRs retain the standard profile. Unknown variable values
stop before model calls. The expanded profile fits the published
windows of [Astra 6](https://developers.openai.com/api/docs/models/gpt-6-astra)
(1,050,000) and [Fable 5.2](https://platform.claude.com/docs/en/models/fable-5-2/overview)
(1,000,000), checked November 14, 2026. Both budgets are totals,
including a 64,000-token output allowance and an 8,192-token formatting reserve.
The estimate includes instructions, tools and the full conversation. Ordinary
text uses UTF-8 bytes as a conservative token estimate. Successful Anthropic
web-result payloads instead use bounded accounting estimates: at most 20,000
for the standard profile or 50,000 for the expanded manuscript profile
for fetched text, 16,000 for a search result block, and 128,000 for a binary
fetch result. These estimates do not change the actual conversation sent to
the provider. Unknown block types and repository text receive no discount.

After a response, the next estimate adds the larger of the new accounting
growth or the reported output-token count to the request's input-token count.
For Astra, the input count comes from reported usage. For Fable, it comes from
the streaming `message_start` input count, including cache reads and writes,
preserved before subsequent updates. End-of-request Anthropic usage can count
the same cached input repeatedly during internal server-tool calls; that
cumulative total is retained for diagnostics, not used as resident context.
If the initial count is missing after server-tool use, the previous preflight
estimate is used instead. The next usable request-start measurement
recalibrates the estimate. Before usable measurements, the full request is
estimated with the same byte and web-payload accounting rules.

Fable's requests cap web search at three uses and web fetch at five uses, with
`max_content_tokens` set to 20,000 for fetched text. Expanded manuscript reviews get
ten searches, twenty fetches, and 50,000 tokens per text fetch. `budget-profile.json`
records the configured variable, changed-path classification and selected limits.
This opt-in does not raise either provider account's spending limit. Direct calls share the
limit across a turn, including client-tool-result and `pause_turn`
continuations; programmatic calls through dynamic filtering reset per
request. Failed or pending direct calls consume the displayed allowance
conservatively. These are not review-wide quotas. Astra has no corresponding
local web-use cap. The fetch text limit is approximate and may truncate the
source; omitted text has not been reviewed. It does not cover binary PDFs.

The search and binary accounting reserves are assumptions, not provider
content limits or proven upper bounds. The guard enforces the selected 400,000- or 900,000-token
**estimate**, not a guaranteed ceiling on actual context or spending. A large
binary result can exceed the estimate within a request; the following
request-start measurement corrects it. Provider-side web tools can add
context during a request. The token-counting
endpoint does not support the gate's server tools, so the gate does not send an
incompatible counting request or silently remove those tools. An independent
tool-result guard permits 1,200,000 characters in the standard profile and
2,700,000 in the expanded profile, proportional to the context budget. Before a file, file-list or
history result is returned, the gate measures the complete projected next
request, reserving small error results for other calls in the same batch and
4,096 tokens for recovery. It also reserves another 64,000 tokens for the
reviewer's own output to enter the next request. An oversized read returns a tool error and leaves
the review running. Every result includes `remaining_context_tokens` and
`remaining_tool_characters`, which are planning estimates rather than exact
token allowances. Every client tool result, including an error, also includes
`web_uses_remaining`: Fable's remaining direct uses, the next request's
programmatic maximum, and the fetched-text truncation warning. Provider-owned
server-result blocks are replayed unchanged. Rejected repository results
neither count as source reads nor complete the history
requirement. The model can retry a smaller read. The pre-request check remains
the final safeguard for unexpected growth, such as a large server-tool result.
When the remaining allowance falls below the reviewer-output reserve, trusted
instructions tell the reviewer to finish now and list everything not reviewed.
The original system prompt, tools and earlier messages remain unchanged to
preserve signed thinking. Runtime guidance is appended after a user/tool-result
message; a Fable `pause_turn` is resumed unchanged before that guidance can be
inserted. See the provider's [append-only instruction rules](https://platform.claude.com/docs/en/build-with-claude/preserved-thinking/change-tools-or-instructions).
A finish-now report records whether source/history reads were admitted. Without
history, every earlier finding stays unresolved in code. Without either read
prerequisite, the report cannot be accepted by collaborator override; a new
review with sufficient context is needed. These completed rejection reports
can still be reused to avoid another automatic charge on the same head.
Required computation failures are checked before each model turn and again
after every provider retry backoff, before a further paid request is sent.

An immediate cross-reviewer stop on a fatal finding is a separate follow-up;
this change does not add a fatal-finding field, shared cancellation flag or a
ban on later automatic rounds specifically because a finding is fatal.
An incomplete necessary check must be reported as a finding with a request for
changes. That blocked decision is permitted even if the reviewer could not
finish its source/history reads; acceptance still requires those reads and
disposition of every prior finding. The gate never silently truncates conversation history or repository
reads, and it does not accept a partial review. This does not make
provider-truncated web content a complete source read.
Scope reads to the changed argument and affected consumers.
Split a review that cannot fit while preserving all necessary dependencies.

Anthropic caching uses a one-hour TTL. This reduces expiration during long
turns, but cannot guarantee cache hits. One-hour cache writes cost 2x base input
price, compared with 1.25x for five-minute writes; cache hits are cheaper. Cache
reads do not count toward the default input-token rate limit, while new input
and cache writes do. Other simultaneous requests can still exhaust the shared
rate limit. These changes do not raise an account spending cap.

Sources: [prompt caching](https://platform.claude.com/docs/en/build-with-claude/prompt-caching),
[rate and spending limits](https://platform.claude.com/docs/en/api/rate-limits),
[token-counting limitations](https://platform.claude.com/docs/en/build-with-claude/token-counting),
[web fetch caps and content limits](https://platform.claude.com/docs/en/agents-and-tools/tool-use/web-fetch-tool),
[cumulative server-tool cache usage](https://platform.claude.com/docs/en/build-with-claude/context-editing#server-side-tools).

## Collaborator commands

A current collaborator with write, maintain or admin access can request a run:

```text
/protocol-b review
```

The check summary prints full finding IDs. To decide a deadlock:

```text
/protocol-b override FULL_HEAD_SHA RUN-ATTEMPT-REVIEWER-FINDING_ID Reason for this decision
```

Post one command per finding. A run checks current collaborator access and the
exact head. It takes the latest completed pair of decisions from this App's
check output, never from a bot comment claiming acceptance. If every new and
unresolved finding is covered, it passes without asking either model to agree.
If a model never completed, the head changed, or a finding remains uncovered,
the override does not pass. The summary records collaborator names and reasons
and states that affected claims are **not outside reviewed**.

## Testing before activation

1. Obtain non-author-family review of the implementation and its repairs.
   Commit the inactive workflow to the default branch only after that review.
2. Configure the App and default-branch-only Environment above. Keep
   `PROTOCOL_B_MODE` unset or `off` until the designated test PR is ready.
3. Set repository variables `PROTOCOL_B_MODE=test` and `PROTOCOL_B_TEST_PR` to
   the throwaway PR number. No other PR receives a test review. Test mode never
   requests auto-merge; its check is named `Protocol B / test review`.
4. Exercise a fork PR. Confirm both exact model IDs, file and web source reads,
   both tool-stream formats, and an App-issued check on the correct head. Test a
   no-argument `read_history` call and a resumed Anthropic `pause_turn`.
5. Introduce an intentional error, observe rejection, repair it, and confirm
   both reviewers address the finding. Test a head change, interruption,
   unauthorized override and authorized override. Confirm an unrelated Actions
   check or forged bot comment cannot substitute for the App's decisions.
6. Verify that a branch or tag workflow cannot obtain the Environment keys.
   Record run links and limitations. Do not describe offline simulated reviews
   as live model validation.
7. After the owner approves activation, preserve all 14 computation checks and
   strict up-to-date protection, require `Protocol B / review` **from the new
   App's integration ID**, enable repository auto-merge, and set
   `PROTOCOL_B_MODE=live`. The ruleset's bypass list must be empty. The owner
   must confirm this and record the ruleset ID, target, active state and date
   in the settings readback before deploying the direct-merge path.
   Verify an authorized throwaway change completes the
   protected merge path. Update the deployment wording to reflect the result.

The workflow checks the required contexts, App pin, strict up-to-date flag
and repository auto-merge setting before either merge path. It cannot
configure them itself. Enforcement of the other rules on the merge request
depends on the deployment condition that the ruleset's bypass list is empty;
the workflow's branch-rules query does not verify that list.

On November 14, 2026, owner Elliot Glazer reported that ruleset `26781429`,
"Main branch PR and CI requirements", is Active, targets `main`, and has an
empty bypass list. He reported that Fable saw the screenshot. This is recorded
as an [owner readback](reviews/activation-2026-11-13/settings-readback.md#owner-readback-november-14-2026),
not as a fresh API verification by this workflow. The condition must remain
true for the direct-merge deployment; a later settings change requires a new
readback before relying on it.

After App acceptance, it reads all required check contexts from the effective
rules, across every page, and their results on the reviewed head. The immediate path requires
completed successful check runs from the required App identities. A legacy
status cannot stand in for an App-pinned check; any same-name legacy status
must also be successful. A check run with no App identity does not match.
Missing, pending, failed, neutral or skipped check
runs do not qualify for the immediate path. The gate's own non-required Actions
job can still be running without preventing that path.

When every required result qualifies, the workflow requests a direct merge
through GitHub's protected merge endpoint, with the exact reviewed head SHA.
It rechecks the head, destination branch and trusted policy before requesting
the merge. It also compares the latest observed default-branch tip to the
reviewed head and requires an integer `behind_by` of zero before the direct
merge request. A missing, invalid or nonzero value, or a failed comparison,
blocks the direct merge. This checks containment independently of GitHub's
strict setting. The comparison uses fixed commit SHAs. A default-branch
advance after the comparison is still subject to GitHub's strict rule under
the empty-bypass-list deployment condition. The merge request's SHA parameter
protects against a changed PR head. When required checks are not all successful,
the workflow requests auto-merge, leaving GitHub to
wait for its merge requirements. An API refusal remains a reported failure;
there is no automatic replay of an uncertain write. Readiness, the compared
commit SHAs and `behind_by`, and merge responses are retained in the run artifact.

If GitHub returns the known `UNPROCESSABLE` refusal that the pull request is
already in clean or unstable status, the gate performs one new
readiness check, including the current rules, required checks, head and policy.
If those checks now pass, it attempts the same guarded direct merge. Otherwise
it reports the refusal. It does not repeat the auto-merge mutation. A transport
failure, HTTP rejection, unknown GraphQL error, or ambiguous partial success is
not treated as that refusal and does not initiate another merge attempt. A null
mutation result alone is not evidence that the write had no side effects.

Merging with the workflow's `GITHUB_TOKEN` does **not** trigger `main`'s `push`
workflows. After a **direct merge**, this gate reads the PR back once and confirms
that it is merged with the reviewed head into `main`. The confirmed commit must
match the PUT response and be contained in `main`. Only then does it dispatch
Research checks and Kernel Lean build and audit, each with `ref: main` and no
inputs. This needs Actions write permission on the workflow token. It does not
change the receiving workflows, the kernel contract, or the check-only App's
permissions, and it sends no environment secrets to the dispatched jobs.

The dispatch uses GitHub API version `2026-03-10`, which returns the new run ID.
The gate reads that exact run and records its `head_sha` alongside the confirmed
merge commit. `main` may advance between merging and dispatching. In that case
the artifact records the difference; it does not pin, rewind, or claim to have
tested the older commit. Both receiving workflows retain their existing
concurrency and cancellation behavior. The dispatched kernel job performs the
full audit because its scope skip applies only to pull-request events.

A dispatched run is not identical to a push-triggered run. The manuscript version
check validates current state; its publication-transition check has already run
on the PR. Dispatched kernel runs neither save the push-only kernel cache nor
serve as push-run base evidence for later PR progress tables. Those tables can
therefore report `not_measured`. This gate change preserves those limitations.

**Deferred auto-merges require a manual step.** The review job does not poll for
them, and there is no closed-PR or `workflow_run` handler. Once a maintainer
confirms a deferred merge, they must open Actions and run both **Research checks**
and **Kernel Lean build and audit** with branch **main**. The same applies if
auto-merge was already enabled. `post-merge-manual.json` records this limitation
in the gate artifact. A successful App check is not evidence of post-merge tests.

For direct merges, `merge-result.json`, `merge-confirmation.json`, and the two
`dispatch-*.json` receipts are retained with the review artifact. Each receipt
records intent before the API call, its response after acceptance, and the
actual run ID, URL and head SHA after verification. A failed or uncertain
dispatch is not retried automatically. The other workflow is still attempted.
Inspect Actions and these receipts before manually starting any missing run;
an accepted dispatch or returned run ID is not evidence that its checks passed.
A failed one-shot merge readback also requires reconciliation before dispatch.
See GitHub's [workflow-trigger rules](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow),
[dispatch API](https://docs.github.com/en/rest/actions/workflows#create-a-workflow-dispatch-event),
and [merge endpoint](https://docs.github.com/en/rest/pulls/pulls#merge-a-pull-request).

## Live-test scope and deferred cases

The owner selected PR69 for the initial live tests: a correct lemma, a deliberate
error, an authorized override of every finding, and repair of the lemma. Each
test must be reported from its actual App check and reviewer records. A same-name
check is excluded at activation by reading back the ruleset's App integration ID.

Observed on November 13, 2026, America/Los_Angeles (PST). The later rows are
November 14 in UTC. Exact UTC times, heads and preserved App outputs are in the
[live-test evidence](reviews/activation-2026-11-13/README.md#live-test-evidence).

| Case and run ID | App evidence | Published reviewer evidence and result |
|---|---|---|
| Correct lemma, `43527659588` | [132237414556](https://github.com/elliotglazer/diophantine-z-q/runs/132237414556) | [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6867595525) and [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6867587047) accepted; App success. |
| Deliberate false lemma, `43540895723` | [132281047204](https://github.com/elliotglazer/diophantine-z-q/runs/132281047204) | [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869397404) and [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869390780) requested changes; App failure with four full finding IDs. |
| Authorized overrides, final run `43541825778` | [132283952957](https://github.com/elliotglazer/diophantine-z-q/runs/132283952957) | No new reviewer verdict: the App used the completed rejection reports above, named `elliotglazer`, and marked the affected claims **not outside reviewed**. All four findings were covered. |
| Repaired lemma, `43542130192` | [132284917858](https://github.com/elliotglazer/diophantine-z-q/runs/132284917858) | [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869581747) and [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869577863) accepted and each marked all four findings resolved; App success without an override. |

The four override review steps lasted 6, 5, 5 and 9 seconds. Their App outputs
show the first three blocked for incomplete coverage and the last successful.
The [preserved timing records and historical override branch](reviews/activation-2026-11-13/README.md#override-execution-evidence)
support the operator's zero-model-calls observation: that branch reads existing
App decisions and does not invoke either model. The downloaded artifacts also
contain no model-turn records. Short duration alone would not prove zero calls;
this is execution-path evidence, not independent provider billing telemetry.

The owner deferred live tests of an interrupted run, an unauthorized override,
and a real Anthropic `pause_turn`. A branch/tag workflow attempting to obtain
the Environment keys has also not been tested. The App pin was read back, but
a deliberate forged-check merge attempt was not run. At this snapshot, a
successful protected live merge and its post-merge workflow trigger have not
yet been observed: PR87 is the activation test and PR88 used owner bypass.
The broader checklist remains a list of obligations and coverage to pursue,
not a claim that these omitted tests passed. The owner activated with these
recorded limitations; the pre-activation review requirement was not deleted.

GitHub has announced a default restriction on public `pull_request_target`
workflows from December 2, 2026. The repository's future Actions-policy setting
has not been verified here. If automatic triggers are restricted, collaborators
can request `/protocol-b review` or use the default-branch manual dispatch;
an absent App acceptance still blocks the protected merge.

## Reproducing offline checks

From the repository root, with Python's standard library:

```sh
python -B -m unittest discover -s tests/protocol_b -v
```

These tests load the actual inline program from the workflow. All model and
GitHub responses are simulated. They require no keys and publish nothing.

For a necessary paywalled source, first reuse an eligible unchanged application
review or find a lawful public primary-source copy. If the changed application
still cannot be checked, identify the exact passage for a collaborator. Do not
buy access or transmit restricted copies automatically; obtain any needed
authorization separately. That application remains unchecked until addressed.
