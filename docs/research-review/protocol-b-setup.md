# Protocol B setup and test checklist

Status: prepared, inactive, awaiting review of the repairs and a live test.
No API keys are included in this repository. The old controller stays retired.

## Identity and credentials

The owner creates a dedicated GitHub App for this gate. Give it only repository
Checks read/write, plus GitHub's mandatory metadata read access, and install it
only on `elliotglazer/diophantine-z-q`. It needs no webhook, code-write permission,
or external server. The retired App identity can instead be reused after
rotating its key, deleting its old keys, removing any other installations and
confirming the old controller cannot use the new key. Do not reuse the retired
controller's key. These setup operations require the owner's authorization;
this document does not assert they have been performed.

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
and requests GitHub auto-merge. Only the App token writes the review check.

## Review behavior

The job runs trusted default-branch code and instructions. It never checks out
or executes the candidate PR. Both approved models receive pinned source reads
and web tools. Reports record actual returned model IDs, source reads and usage.
There is no fallback model. Unavailable sources, unfinished reviews and changed
heads do not pass.

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
findings are supplied to later reviews. HTTP failures are logged
as infrastructure failures, not invented mathematical objections. Initial 429
and 5xx responses from a model provider get at most two retries. Partly received
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

The 8,000,000-character tool-result guard is a runaway-input limit, not a model
token-window estimate. It excludes instructions, conversation output and other
provider accounting. A provider can reject a request for context length first;
the error is retained and the review fails without acceptance. Scope source
reads to the changed argument and affected consumers. The full-manuscript
offline simulation tests data handling, not whether that whole input fits in
either model's context. Actual review capacity remains part of the live test.

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
   `PROTOCOL_B_MODE=live`. Verify an authorized throwaway change completes the
   protected merge path. Update the deployment wording to reflect the result.

The workflow checks these merge settings before requesting auto-merge. It
cannot configure them itself. It never bypasses the ruleset.

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
