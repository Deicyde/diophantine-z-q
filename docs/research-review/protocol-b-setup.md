# Protocol B setup and test checklist

Status: the owner activated Protocol B for future pull requests on November 13,
2026, America/Los_Angeles. Astra's authenticated readback at 18:57 PST that day
(November 14, 02:57 UTC) observed live mode and the App-pinned requirement.
See the [settings evidence and limits](reviews/activation-2026-11-13/README.md)
and [pre-activation review record](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/docs/research-review/reviews/pre-activation-reviews.md). This is
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
There is no fallback model. Unfinished reviews and changed
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

Each finalized round also posts a readable summary before its compact JSON
metadata. It shows both reviewer decisions, blocking findings, qualified
source-access limitations and overrides, and the next step. Long lists show
the first ten entries and explicitly link to the complete App check and
original reports. The summary never replaces those records or rewrites a
reviewer decision. Failure to post this explanatory comment is recorded in
the run artifact and does not invalidate the App result or prevent a protected
merge. The gate excludes its own summaries from new review history.

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
not grant override authority. The dedicated App's records determine the
findings; authorization requires a current admin's new, unedited comment.
The gate checks GitHub's edit metadata and the exact current body, so changing
someone else's admin-authored comment cannot create an admin decision. Preserve substantive objections in the
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

Before the first request, if its estimate would exhaust the output and recovery
reserves, the gate defers inline patches from that unsent packet. Every changed
file, all other file metadata and available hunk ranges remain. Reviewers must
fetch the affected sources and necessary context; deferral does not reduce the
review scope. Metadata that still exceeds the budget fails the existing hard
guard. No earlier conversation or source read is removed. The durable report's
`initial_packet` field records whether patches were deferred, their count and
the total changed-file count, even if the optional reuse binding is omitted.
The run artifact `<family>-initial-packet.json` also lists the deferred paths
and before/after estimates. Historical reports without this field do not make
a deferral assertion.

Old-side hunk ranges use GitHub's PR merge base; `read_file(base)` instead serves
the pinned current base tip. New-side ranges use head. The packet supplies the
verified `merge_base` SHA when patches are deferred, also retained in the durable
marker. The read tool still accepts only head/base revisions. The SHA identifies
the old revision but does not provide a supported retrieval route for both
reviewers. On a diverged base, old-side text may be unverifiable: the reviewer
must verify it independently or report the limitation and request an updated
branch before acceptance, not assume the old range
matches the current base. Deferred hunk ranges are navigation hints, not source
text or evidence that the removed passage was read.

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
prerequisite, the gate records an explicit incomplete-review scope item. An
admin may override it with the missing coverage still recorded as incomplete. These completed rejection reports
can still be reused to avoid another automatic charge on the same head.
Required computation failures are checked before each model turn and again
after every provider retry backoff, before a further paid request is sent.

An immediate cross-reviewer stop on a fatal finding is a separate follow-up;
this change does not add a fatal-finding field, shared cancellation flag or a
ban on later automatic rounds specifically because a finding is fatal.
An incomplete necessary check belongs in the unreviewed-scope list with a
request for changes. It creates an administrative scope item rather than a
mathematical-error finding. Without an explicit admin override, incomplete
coverage remains blocking. The gate never silently truncates conversation
history or repository reads and never labels a partial review complete. This does not make
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

The check summary prints full finding and scope-item IDs. Only a current
repository admin may decide a deadlock:

```text
/protocol-b override FULL_HEAD_SHA RUN-ATTEMPT-REVIEWER-FINDING_ID Reason for this decision
```

Post one command per finding or scope item, using its full displayed ID. A run
checks current admin access and the exact head. It takes the preserved review
records from this App's check output, never from a bot comment claiming acceptance.
If every blocking finding other than a qualified source-access limitation,
and every incomplete-scope item, is covered, it passes
without another model call. A stale head, wrong model or uncovered item still
blocks. The summary records the admin and reason and states that affected
claims are **not outside reviewed**. An incomplete review stays recorded as
incomplete after the override.

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


## Review continuity and source-access limitations

Elliot authorized these rules on November 14, 2026. This change does not alter
the designated App, keys, ruleset, approved models, merge permissions or override
permissions.

An acceptance is retained for the exact head even if the other reviewer needs
another round. The accepting model is not called again. The evidence must be a
completed review by the exact approved model in the designated App's own check,
bound to this PR. Bot comments only locate those checks. A later transport failure
does not erase an earlier acceptance. Reuse requires the same trusted workflow and reviewer instructions as the
original review. Changed gate policy invalidates retained reviews; there is no
author-maintained compatibility file. Previously undispositioned findings still block. The latest completed verdict from each reviewer supersedes its earlier verdicts across heads. If it cannot be reused, that reviewer must run again; an older acceptance cannot be revived. An incomplete or failed attempt does not erase a completed verdict.

New reports attempt to store an optional rebase binding for the complete diff,
the source passages actually returned at head or base, both sides of diff hunks
whose text was displayed in the initial packet, and file-discovery results.
Deferred patches and their hunk ranges do not count as displayed or read text;
subsequent admitted source reads still count. The complete original diff remains
the change identity. Diff old-side passages use the pinned merge-base commit;
an explicit `read_file(base)` still uses the pinned current base tip. Hunk text
and counts of displayed hunks must match those source revisions before a binding
is made or reused. A binding can also be omitted for output capacity; the durable
`initial_packet` marker remains in the report independently of that binding.
A deferred review whose merge base differs from its reviewed base tip gets no
rebase binding: necessary merge-base reads through web tools are not tracked.
The reuse consumer also rejects such a report across heads, even if it contains
a binding. Same-head retention remains available under the existing rules.
If the merge base or displayed passage identity cannot be established, rebase
reuse is disabled. Older bindings without this distinction cannot authorize a
new head. After a rebase, each exact passage must occur uniquely
in both its original and its new file; movement of line numbers is allowed, edits inside the passage
or an ambiguous duplicate require fresh review. Repository PDFs requested
through read_file and mandatory policy inputs, including the workflow, retain
whole-file identities. An unavailable or truncated diff cannot authorize reuse.
This permits disjoint edits in one manuscript while preserving the dependencies
the reviewer actually examined. It does not establish that an unread passage is
irrelevant; finding the relevant dependencies remains part of the source review.
Older reports without the current binding can be reused at their original head,
but not after a rebase.
A complete negative verdict may carry across an unchanged rebase without
repeating its cost; `/protocol-b review` asks the non-accepting reviewer to try
again. Original head/run/attempt remain intact and `reused_for` records the new
head. `review-reuse.json` records the source App check IDs. Current CI, head and
protected-merge checks still run normally.
An override remains bound to its original head and current authorization; a
conditional acceptance does not carry that override across a rebase. Reuse-only
runs do not consume or exceed the four-paid-automatic-round limit. The override
consumer accepts an App-authenticated effective head after rechecking the rebase
binding, but still requires authorization for every finding on the current head
except qualified source-access limitations.

Each new report records a fixed-size digest of the complete discussion and
interrupted-observation snapshot admitted to that review. The snapshot itself
is preserved in the run artifact. A newly observed comment cannot disappear when separate acceptances
are combined. If a reviewer already needs to run, it receives that history. If
both proof reviews are retained, one reviewer assesses a supplement about the
unexamined observations instead of repeating the unchanged proof audit. A last
history read before acceptance detects observations arriving during the run.
Missing history coverage blocks model acceptance. An authorized override does
not require a further paid review merely because a comment was added. The four-paid-round limit also
applies to automatic supplements. A supplement retains the union of the original
proof review and supplemental source dependencies; missing original bindings
disable rebase reuse.

Original policy refs remain recorded. Both exact-head and rebase reuse retain
the existing same-policy requirement. A changed head must also pass the rebase
binding, including the workflow's whole-file identity.

Reviewers give structured source checks for every published passage opened for
a changed application, even before an access finding exists, and also record
unavailable passages. An
access-only finding is nonblocking only if every named source passage has a
matching `verified` check from the other approved reviewer. That check attests
both reading the exact passage and checking its application without objection.
The history tool exposes the earlier reports' structured source checks, so a
reviewer can use the exact peer passage ID in a later round. No keyword matching
guesses that an older untyped objection was access-only.
When the same source remains unavailable in a later round, the reviewer keeps
the original full finding ID in both `prior_findings` and `access_limitations`,
and keeps the exact source IDs. It does not create another new finding for
that same access failure. The original finding and the reviewer's actual
decision remain visible. Each named passage still needs the other reviewer's
verification; an unqualified older finding is not silently merged with a new
one. A distinct mathematical objection is assessed separately.
Missing arguments, mismatched hypotheses, missing review history, incomplete
review and context exhaustion remain blocking. The original verdict and finding
are retained; the check and artifact list the limitation and which reviewer
verified its sources. This is not a collaborator override or a claim of unanimous
source inspection. Both reviewers' findings must otherwise be resolved.

The same-head and rebase paths do not use candidate code, credentials or
candidate-supplied approval files. The offline continuity suite checks partial
acceptance reuse, approvals from separate rounds, wrong App/PR/model rejection,
changed diffs/dependencies, retained negative decisions, and matching versus
mismatched source-access evidence. The standard/expanded profile controls are
unchanged by this implementation.

Optional rebase bindings are omitted if they would overflow a permanent comment
or the combined App check payload. The completed verdict and every finding are
retained; the omitted binding remains diagnostic evidence in the run artifact,
but cannot authorize rebase reuse. No substantive finding is truncated.

A completed App check that validates reuse for a new head establishes that exact
effective head. Dropping its optional binding does not invalidate unchanged-head
retention or a current authorized override; any subsequent different head still
requires a valid binding or a fresh review. Original review provenance is kept.

Supplements retain source attestations with their original reviewer, head, run
and policy. A new check for the same source ID supersedes the retained one,
including an explicit withdrawal recorded as unavailable. Later unrelated
supplements cannot revive withdrawn verification. The combined decision and
history tool use this evidence without claiming a fresh inspection occurred.

Superseded attestations are removed from the inherited copy; surviving entries
retain compact original provenance. If this evidence still exceeds output
capacity, the full omitted data stays in the run artifact and cannot authorize
source-access relief. This also applies to current source checks when two valid
fresh reports exceed the combined App payload limit. Omitting current checks
also removes that report's inherited evidence, so a removed withdrawal cannot
expose an older verification. The decision is recomputed before publication. Completed
verdicts and findings remain, including a rejecting supplement; missing evidence
does not revive an older acceptance or a withdrawn source verification.


### Source-access relief when other findings need a decision

A source-access limitation qualified by the other reviewer's exact-passage
verification does not need a second, explicit override when a separate
substantive finding blocks the same round. The gate records that limitation
even while the other finding remains blocking. It requires an override only
for the remaining unresolved findings. Every active occurrence of an ID must
qualify for source-access relief: a substantive objection by either reviewer
cannot disappear because the other report calls the same ID access-only.
Original reviewer decisions and source evidence remain in the record.

When all unresolved findings are qualified access limitations, an override
command does not grant acceptance. It directs the operator to an ordinary
review, which checks discussion coverage, prior dispositions and computation
status. A malformed, stale-head or unknown-ID command cannot replace that review.
In a mixed case, an authenticated override of the remaining substantive findings
uses the existing human-decision path without another model call, including
when there is new discussion. Qualified limitations stay recorded if some other
finding still lacks an override; the overall check remains blocked.


## Blocking findings and nonblocking notes

Fresh findings carry a severity, `blocking` or `note`. Blocking findings identify
a substantive error, a specific unclosed gap, or a source-access limitation
under the existing peer-verification rule. A gap must locate the missing step
and record an attempt to close it, including the obstruction that remains.
Pure wording, naming, typography, style and optional exposition are notes.
A short implicit step reconstructed from the existing argument is an expository
note, with its derivation. A previously recorded substantive gap still follows
the audit-integration rule: its repair must be located in the current primary
proof source or cited result and incorporated at the consuming step. A new
load-bearing proof appearing only in a reviewer report does not close it.
The contributor need not fix those notes for this PR to pass.

Reports also state `scope_complete`. Unread work and an interrupted or exhausted
review cannot become an acceptance merely because no mathematical error has
been found. A completed review with only editorial notes meets the review
requirement, even if its original decision says `changes_requested`; that
original decision remains visible, and the gate does not call it unanimous
acceptance. Substantive findings and unresolved earlier findings still block.
Historical reports without severity retain their blocking meaning. Earlier
findings require an explicit disposition grounded in the current argument.

Set the repository variable `PROTOCOL_B_NOTES_ISSUE` to the number of an open
issue in this repository used for optional cleanup. After finalizing a round,
the gate appends its nonblocking notes there with their original finding IDs,
locations, PR head and App check. Reused notes are not posted again. The full
reports and a `nonblocking-notes.json` artifact also retain them. If backlog
delivery fails, the original PR report remains durable, the failure is recorded,
and it does not change review acceptance or stop a protected merge.

This change does not introduce the separate one-round or Lean profiles. Until
those profiles are deployed, the existing reviewer and computation requirements
still apply.


### Admin decisions on incomplete review

Only a current repository admin can override an item, both when the command is
received and when stored override comments are read back. A non-admin override
has no effect and receives a short explanation. Write-access collaborators keep
automatic reviews, `/protocol-b review`, and ordinary protected merge access.

Incomplete review is always presented as an explicit administrative item with
ID `scope-RUN-ATTEMPT-REVIEWER`. This covers unfinished scope, missing required
source/history reads, rejection without an actionable finding, and a review
that did not start or complete. Its record includes the unreviewed work or says
that no itemized list was produced, with links to the original records. This is
not a finding that the mathematics is false. An admin may accept the item with
the ordinary exact-head override command and a reason. The resulting App record
and summary say the PR was accepted with incomplete reviewer scope; they do not
change an incomplete execution or rejecting model verdict into acceptance.
A long unreviewed-scope list stays in the original report and artifact; the App
record retains its hash, item count and location instead of overflowing the
check. The scope item remains incomplete and explicitly overridable.
Even if neither model review ran, an admin can accept the two recorded scope
items explicitly; the resulting record still says neither review ran.

Every remaining substantive finding also needs its own resolution or override.
An override must come from the App's records for the current head and policy.
Stale-head and wrong-model protections, required computations, and the protected
merge rules still apply. Runtime coverage records for missing reviews explicitly
say no model verdict was produced; they do not invent a model execution.

For gap findings, the attempted-resolution text-length minimum merely rejects
empty or near-empty fields. It does not certify the quality of the attempt.
The reviewer must actually attempt the derivation or check the relevant source.
Backlog notes are grouped into bounded comments per round, with individual note
markers retained so reused notes are not duplicated.

### Unedited admin commands

Only repository admins may override reviewer findings. The gate checks current
admin permission when receiving a command and again when reading stored override
comments. Edited comments are not accepted, including edits made by an admin;
post a new comment instead. Both timestamps and GitHub's `lastEditedAt`/`editor`
metadata must establish an unedited comment with the matching body and author.
Missing metadata fails closed. A non-admin collaborator's override has no effect
and receives a short reply. The gate's ignored-override replies do not alter the
reviewed discussion digest or trigger paid supplements. Write-access collaborators retain automatic review, `/protocol-b review`,
and ordinary protected merge access. This change does not alter any review,
computation, head-binding or merge requirement.


### Preserving findings when delivery fails

An absent or incomplete review carries unresolved obligations from the PR's
App-authenticated earlier records across heads. An empty later record cannot
erase a prior objection. These carried obligations are runtime metadata, separate
from the original model verdict, and each still requires resolution or an
exact-head admin override in addition to any scope item.

If posting a completed report fails, the completed verdict remains in the App
record and original artifact. A final report with a form error returns feedback
to the reviewer for correction. If that correction is interrupted, its delivered
substantive findings remain blocking in the recorded incomplete review. Runtime
records saying no model reviewed the PR do not consume automatic review rounds.

Each completed verdict is atomically checkpointed before any report comment is
posted. Working-comment delivery cannot discard a delivered final verdict.
If a report comment contains an objection that never reached an authenticated
App record, the gate preserves it as an explicitly unverified report-comment
claim, with its original ID, comment location and hash. This does not authenticate
its asserted model identity or grant approval. It requires review or its own
admin decision; overriding only missing-review scope does not erase it. App-only
findings whose report comments failed can still receive exact-head admin decisions.


Before either ordinary acceptance or an override, the gate reconciles outstanding
App-recorded findings and report-comment claims, including an interrupted later
round. Unmatched comments are unverified allegations, not model authentication.
They need a disposition or their own explicit admin decision; accepting only
missing scope cannot erase them. Retained acceptances receive a scoped supplement
when they have not addressed a newly recorded objection. The final publication
rechecks these obligations even after an otherwise successful decision.

Report delivery is recorded separately from the reviewer's verdict. A failed
delivery is retried at finalization after checking whether the exact original
comment already arrived. If it still fails, the App record names the original
run artifact and withholds merge; it does not claim the report is on the PR.
Optional reuse-metadata failure does not suppress the report delivery attempt.
A scoped supplement retains its original-review identity independently of that
optional metadata. No paid verdict is replaced with an empty failure record.

A later run may reconcile the exact original comment by its saved body hash.
If only a compact App record remains and that comment is absent, publication
stays blocked until the full original report is recovered from its run artifact.
The compact record is never reposted as the original prose, source list or notes.
Failure-report delivery uses the same guarded path, so one worker's notification
failure cannot prevent the other worker's actual final result from being collected.

A scoped supplement inherits outstanding publication obligations from every
retained proof review in its chain. Its own delivered report does not satisfy
those obligations. The gate checks the original comment hashes and withholds
merge until each original report has arrived. Malformed final-output containers
are treated as diagnostic data; failure processing is isolated per worker so
it cannot interrupt collection of the peer reviewer's verdict.
