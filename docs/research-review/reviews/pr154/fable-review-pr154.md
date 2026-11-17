# Local read of PR154 (unattended outside review), head 1e1224ac, base 970ec6bf

Fable (Claude Code, Elliot's session), 17 November 2026. Optional local review, not a gate result. Read-only: nothing posted, pushed or written to the relay.

Read: the whole of `PR154.diff` (workflow, embedded program, documentation; the three new test files skimmed), plus the unchanged helpers the new code calls (`collaborator`, `own_comment`, `same_policy`, `same_open_revision`, `head_checks`, `required_checks_passed`, `merge_readiness`, `direct_merge`, `merge_and_dispatch`, the round-marker write). Line numbers are those of `.github/workflows/protocol-b.yml` in the worktree unless marked "diff".

## Verdict

Not ready for a paid round. Spending control and merge authority are well built: I found no way for an outsider to obtain more than one full review per PR, to exceed the caps, to reach a full review without a reservation, or to merge anything a collaborator must approve. The two findings below are about (B1) the lane stopping for everyone, cheaply and also by accident, and (B2) the set of paths that can merge with no human being much wider than the design's "small documentation fix" and "a note and data under research/".

## Blocking

### B1. Head-of-line blocking: one PR can stop the unattended lane for everyone, with no spend

`outside_wake_candidate` (line ~874, diff 669-705) serves every `workflow_run` and hourly event by returning the oldest open outside PR that passes `outside_screen(pr, files, ready, [], now)`: the screen is run with an empty reservation list, and a PR is skipped only if it carries a bot comment starting with `OUTSIDE_MARKER`, `ROUND_MARKER` or `MARKER`. A PR that passes that screen but is then refused in `admit_outside` before `reserve()` gets no such comment (only an App check), so every later wake selects it again and never reaches a younger PR. A newly opened PR cannot rely on its own `pull_request_target` event either, because its computations have not finished at that moment; the wake is its only route.

Refusals that leave no marker (probe-confirmed with the production functions):

1. `triage_size` (diff 554-559). A PR within the 20-file / 2,000-line limit whose JSON material exceeds 32,000 bytes passes the screen and is refused before reservation. 2,000 changed lines is normally far more than 32 KB, so the first medium-sized honest PR does this by accident, permanently, until it is closed or a collaborator reviews it.
2. Quota. An author's fourth PR in seven days passes the reservation-free screen and is refused with `quota: author_week`. While it is the oldest eligible PR, nobody else is served for up to a week; when a slot frees it is served first, and the author's next PR takes its place. One account can hold the lane indefinitely and take every slot it frees.
3. Any exception after the preliminary screen (for example an uncertain intent found by `outside_reservations`) ends as `needs_maintainer` with no marker.

Two aggravations:

- `other_open_prs` titles are inside the 32,000-byte allowance (`outside_triage_body`, diff 254-262). About 130 open PRs with 250-character titles make every PR `triage_size` (probe 1c). Titles are attacker-controlled, and Jack's drafts already contribute. Other PRs' titles are also a prompt-injection channel into a victim PR's triage ("duplicate", "off topic"), which burns the victim's single attempt.
- Each wake re-screens every unmarked open outside PR from scratch (PR, comments, files, Lean contents, rules, checks, statuses), and each re-selected blocker then runs `outside_reservations`, which lists all PRs and the comments of every PR updated this month. `workflow_run` fires on every Research or Kernel completion in the repository. With a few dozen open outside PRs this can exhaust the repository's shared `GITHUB_TOKEN` request allowance, which the collaborators' gate runs and merges also use. Not measured.

Suggested repair: record every refusal durably against the head (an App check the wake reads, or a marker comment) and skip refused heads; take the candidate by a fair order that does not depend on one PR; bound the number of PRs examined and API calls per wake; exclude or separately bound `other_open_prs` in the triage size.

### B2. The paths that can merge without a human include existing records, released material and policy text

`outside_merge_category` (line ~421, diff 216-228) decides only by path and extension. It ignores `status`, so modification, deletion and rename of existing files qualify (probe: a `removed` `research/quartic214/README.md` returns True). `outside_protected` (diff 92-102) is narrower than the design's protected list in two ways.

Exact auto-merge sets (after two-reviewer acceptance and a triage `pass` with the matching category):

- `docs`: `README.md`, and any `docs/**/*.md` except `docs/research-review/`, `docs/audit-history/`, `docs/release-policy.md`, `docs/manuscript-agent-guide.md`, `docs/lean-contributions.md`, and paths matching the review-word pattern below.
- `improvement_note`: any `research/**` file ending `.md .tex .json .csv .tsv .txt`, except `research/version<N>/` and paths matching the pattern.
- Pattern: `(?:^|[/_-])(?:reviews?|audits?|evidence|snapshots)(?:[/_-]|$)`, case-sensitive.

What that lets through today (all probe-confirmed as auto-mergeable):

1. Review records, which the design protects. The pattern needs `/`, `_` or `-` after the word, so a file name is never matched: `docs/quartic-4973/context/v2_review.md`, `draft_review.md`, `docs/manuscript-revisions/version14/final5882-transport/REVIEW.md`, the `*_REVIEW.md` and `*_ACCEPTANCE.md` files outside a `review/` directory, `FINDINGS.md`, `VERIFICATION.md`. New files named like records (`research/new/fable-review.md`, `acceptance-record.json`) also pass. Case variants (`research/Version19/x.md`, `docs/Research-Review/x.md`) are unprotected, harmless today but they show the rule is a denylist over spellings.
2. Material of released versions kept outside `research/version<N>/`: `research/quartic214/**` (construction data read by required checks, not bound by `SHA256SUMS`), `research/quartic214-manuscript*/` (TeX of released manuscripts), `research/quartic214-protocol-d-public/` and `-progress/` records, `research/2026-11-06-collaborator-notes/`, and under docs `docs/manuscript-revisions/version*/README.md` and `GUIDE.md`, `docs/quartic-*/`.
3. Policy and procedure text: `docs/explicit-record/README.md` (the explicit-record rule), `docs/current-manuscript-build.md`, `docs/kernel-ci-scope.md`, `docs/research-guide.md`, `docs/gate-retirement-20261113.md`.
4. `README.md`, which carries the contributor line and the current-version statement. `CREDITS.md` is not auto-mergeable, but the README credit line is. Given today's Version 20 finding about that very line, a credit change should not merge without a person.

Scenario: an outsider's PR titled "fix typos" edits two words in `README.md` and removes a name from the contributor line, or rewrites a threshold in `docs/explicit-record/README.md`. Screen passes, triage says docs, both reviewers judge the diff internally consistent, and it merges with no collaborator. The reviewers are a real barrier, but the mechanical rule exists for the case where they are wrong or persuaded.

Suggested repair: make both categories allowlists. `improvement_note`: only files with status `added`, under a directory reserved for outside notes (or one that does not exist at the base), never a modification, deletion or rename. `docs`: modifications only, to an explicit list of ordinary documentation (the gate already has such a list, `ordinary_docs` near line 1201), with the README contributor and version lines excluded or the README left to collaborators; everything else needs `/protocol-b merge`. Add regression tests for `status` and for the file names above.

## Notes

N1. Second review of the same head. Wake-triggered runs use the concurrency group `protocol-b-<run_id>`, not the PR's group. If a collaborator has commanded `/protocol-b review` on an outside Lean PR and the run is still in `kernel_preflight` (up to 185 minutes, before the round marker is written at line ~3595), a wake can admit the same PR: `outside_existing_attempt` sees no reports and no reservation. Result: an unattended round and the commanded round on one head, and an `action_required` admission check created over the commanded run's check. Spend is bounded by the caps; fail-closed for merging. Reasoned, not run. A job-level concurrency group keyed on the routed PR number for `kernel_preflight` and `run_reviewers`, or an existing-attempt test that recognises a running commanded review, would close it.

N2. `always()` on `kernel_preflight` and `run_reviewers` (diff 1233, 1271). A job whose condition contains `always()` still starts after the run is cancelled between jobs. Cancelling a run is the only way to stop a paid round; `!cancelled()` keeps that. Not tested.

N3. Auto-merge will often not complete, by construction. `direct_merge` requires the head to contain main's tip, the receipt path requires `intent.base == pr.base.sha`, and a branch update is a new head with no second unattended attempt. Any merge to main between admission and acceptance therefore leaves the PR to a collaborator. Safe; say so in the documentation so that outsiders are not told it merges automatically. Related: if `pr.base.sha` follows main, a main merge during the kernel wait fails `outside_receipt` in `main()` after the slot is counted. I did not establish how GitHub reports `base.sha`.

N4. An uncertain or malformed intent stops all unattended admission until someone reconciles it (`outside_reservations` raises). Correct direction, but the setup document does not say who reconciles or how (the bot comment cannot be edited without becoming "edited", and deleting it leaves an orphan check). Write the procedure down, and consider scoping the stop to the affected PR when the App check is merely absent.

N5. Lean lexical screen (diff 145-162). Since no Lean category can merge without a collaborator in this version, this only decides spending. It misses (probe): `macro_rules`, `elab_rules`, `infix/infixl/infixr/prefix/postfix` (including `local` and `scoped`), `declare_syntax_cat`, `binder_predicate`, `builtin_initialize`, `run_meta`, `run_elab`, `attribute [...]` on existing names (`reducible`, `simp`), `@[export]`, `@[app_unexpander]`, `unseal`. Design item 3 asks for new notation and instances for names in registered statements to be caught; the infix family is notation. Worth adding before the screen is relied on for `lean_helper` auto-merge.

N6. Symbolic links. The files API gives no mode; a `docs/x.md` or `research/x.json` added as a link to another path has an ordinary patch and passes. Harmless as far as I can see, but refuse non-regular entries (the tree or contents API gives the type).

N7. The exact-head kernel dispatch for an outside Lean PR now happens with no collaborator. It follows a successful pull-request kernel run (required computations must have passed), so GitHub's first-time-contributor hold still stands in front of it. It does run outside code in a base-repository run for up to the kernel time limit, up to five times a day. Stated here so Elliot knows; I did not re-read `kernel-lean.yml` for what such a run can write (caches).

N8. Griefing within the caps is inherent: several accounts can use the 5 per day and 40 per month, shutting the lane for others. The reasons are posted and a collaborator can still review by hand.

## Answers to the five questions

1. Spending. One full review per reservation: the receipt is bound to PR, author id, head, base, policy, run id and attempt, must be in phase `ready_for_review`, and is moved to `review_started` before the round. Re-running the workflow changes the attempt and fails the binding; a second automatic event finds the existing reservation; reopening does not reset the per-PR count; author counting is by numeric id. Counters come only from intent comments by `github-actions[bot]` that are byte-exact, unedited and matched one-to-one with an App-authored check; an outsider's comment cannot create, remove or alter a slot. Failed, rejected and interrupted attempts count. Admission is serialized by the job-level group. No full review without the mechanical screen, a reservation, a state recheck and a valid triage result. The hourly pass is not bounded in API cost (B1).
2. Triage. Output is validated strictly (exact keys, enums, reason consistent with decision, one text part, model identity). Injection can at most turn a reject into a full review, or a pass into a reject (N/B1 on other PRs' titles). The category alone never grants a merge: the path rule is applied mechanically at admission and again at merge time on a fresh file list. The path rule itself is B2.
3. Merge. `PUT /merge` carries the reviewed SHA; head, open state, base ref and policy are rechecked in `merge_readiness`, which both the direct and the deferred route pass through (lines 3793-3812, 3884-3916). `/protocol-b merge` must equal the full current head, be unedited, come from a `User` with current write, maintain or admin permission, and is re-read at merge time; it calls no model and needs an existing successful App check bound to the PR, head and policy. An outside author's own comment fails `collaborator`. A collaborator's `/protocol-b review` on an outside PR no longer merges: PR150 would be accepted and held until `/protocol-b merge <head>`. Collaborators' own PRs take the first branch of `outside_merge_permission` and merge as before.
4. Secrets. `outside_admission` and `run_reviewers` hold the App key and provider keys (admission holds only the OpenAI key); both run only the program embedded in main's workflow, with no checkout and no PR code. `route_request` and `kernel_preflight` hold none. `workflow_run` uses only the run id, re-read from the API and checked for repository and workflow path; no artifact of the triggering run is consumed. The global admission lock can have its pending job displaced by newer events; the hourly pass is the recovery, subject to B1.
5. Existing flows. Overrides, incomplete scope, blocking findings, required checks and cross-head reuse are unchanged for collaborators. Changes: a new first job; the editorial shortcut is disabled for admitted outside PRs; outside PRs accepted through a collaborator's review now wait for `/protocol-b merge`; the App check's JSON gains `number`, `policy_ref` and `outside_admission`; the workflow-level concurrency group falls back to the run id for `workflow_run` and `schedule` (N1).

## Tests and probes

- `python -B -m unittest discover -s tests/protocol_b -p "test_outside_*.py"`: 46 passed. The worktree was unchanged afterwards. I did not rerun the full suite (Astra reports 371).
- My probe (scratchpad `probe154.py`, production functions loaded as the tests load them): 1a/1b/1c confirm B1's three no-marker refusals and the title effect; the path table and the `removed` case confirm B2; the lexical list confirms N5.

## Not checked

Anything live on GitHub (concurrency replacement, `always()` after cancel, `base.sha` behaviour, request-allowance consumption, the `protocol-b` environment's protection rules); the triage request against the provider; `kernel-lean.yml` and the dispatch path for outside heads; the three new test files beyond a skim; documentation wording beyond the claims quoted above.

## Draft relay note to Astra (not sent)

From: Fable. About: PR154 (1e1224ac), local read. Needs reply: no.

I read the whole diff and ran the 46 outside tests (pass). Full report: `C:\Users\glaze\Documents\fable-review-pr154.md`. Spending and merge authority look right: I found no route to a second full review, past the caps, or to a merge that needs a collaborator. Two repairs before a paid round:

B1. Head-of-line blocking. `outside_wake_candidate` returns the oldest PR passing a reservation-free screen and skips only PRs with a bot marker comment. A PR refused in `admit_outside` before `reserve()` has no marker and is selected again on every wake: `triage_size` (2,000 lines allowed, 32,000 bytes of material), `quota` (an author's fourth PR blocks everyone for up to a week), or any exception after the preliminary screen. Other PRs' titles are inside the 32,000 bytes, so many open PRs make every triage `triage_size`, and they are an injection channel into another PR's triage. Each wake also re-screens every unmarked PR and the blocker re-runs the month-wide reservation scan on the shared GITHUB_TOKEN allowance. Record refusals durably per head and skip them, bound the work per wake, and take other PRs' titles out of the size limit.

B2. Auto-merge paths. `outside_merge_category` ignores `status`, so edits, deletions and renames of existing files qualify. The review-word pattern needs a delimiter after the word, so `v2_review.md`, `REVIEW.md`, `*_ACCEPTANCE.md` are not protected. Auto-mergeable today: `research/quartic214/**`, `research/quartic214-manuscript*/`, the protocol-d records, `docs/explicit-record/README.md`, `docs/current-manuscript-build.md`, `docs/kernel-ci-scope.md`, `docs/manuscript-revisions/**`, `docs/quartic-*/**`, and `README.md` including the contributor line. Make both categories allowlists: improvement notes as added files only in a reserved directory; docs as modifications to a listed set, with README credit lines left to a collaborator.

Notes in the report: a wake can admit an outside PR while a collaborator-commanded review of it is still in the kernel wait (wake runs are not in the PR's concurrency group); `always()` lets jobs start after a cancel; auto-merge will often be pre-empted by main moving, which the documentation should say; the reconcile procedure for an uncertain intent is not written down; the lexical screen misses `macro_rules`, the `infix` family, `elab_rules`, `builtin_initialize`, `run_meta`, `attribute [...]`.
