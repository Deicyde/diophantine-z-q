# Protocol B activation evidence

This is the November 13, 2026 (America/Los_Angeles) activation snapshot prepared
for PR87. Astra collected the GitHub records through Elliot Glazer's authorized
session. It records deployment observations and test results, not a new review
of the mathematical manuscript or a substitute for independent gate review.

## Settings observation

[settings-readback.md](settings-readback.md) preserves the nonsecret fields
read through GitHub's authenticated API at `2026-11-14T02:57:00Z`, or November
13 at 18:57 PST. At that time, Astra observed:

- `PROTOCOL_B_MODE=live` and repository auto-merge enabled.
- Effective `main` rules requiring all 14 computation checks, strict
  up-to-date checks, and `Protocol B / review` from App integration `5663093`.
- The `protocol-b` Environment's sole custom deployment pattern was branch
  `main`, with no tag pattern. Its App ID variable was `5663093`.

These are attributed operator observations. An anonymous reader may not be
able to retrieve every setting, and this snapshot is not a guarantee that
settings remain unchanged. The [public ruleset](https://github.com/elliotglazer/diophantine-z-q/rules/26781429)
provides a separate current view where GitHub exposes it. No secret values were
requested or exported. The snapshot does not establish key rotation, removal
of old installations, absence of repository-level key copies, or a live test
that a branch/tag workflow cannot obtain the Environment keys.

## Live-test evidence

[live-tests.md](live-tests.md) records the exact heads, App check IDs,
workflow revisions, UTC timestamps and review-step timings. Each `check-*.md`
file contains a JSON block preserving selected fields of the GitHub Check Runs API response, including
the App identity and complete output. Each reviewer Markdown file contains a JSON block preserving the report
published in the linked GitHub comment, with its publisher and timestamp.
These are JSON copies of source records, not new approvals or cryptographic
attestations of the provider's identity.

| Test | App check and retained output | Published reviewer reports |
|---|---|---|
| Correct lemma, run `43527659588` | [132237414556](https://github.com/elliotglazer/diophantine-z-q/runs/132237414556), [copy](check-132237414556.md): success | [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6867595525), [copy](run-43527659588-astra.md); [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6867587047), [copy](run-43527659588-fable.md): both accept. |
| False lemma, run `43540895723` | [132281047204](https://github.com/elliotglazer/diophantine-z-q/runs/132281047204), [copy](check-132281047204.md): failure | [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869397404), [copy](run-43540895723-astra.md); [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869390780), [copy](run-43540895723-fable.md): both request changes. |
| Repaired lemma, run `43542130192` | [132284917858](https://github.com/elliotglazer/diophantine-z-q/runs/132284917858), [copy](check-132284917858.md): success without override | [Astra](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869581747), [copy](run-43542130192-astra.md); [Fable](https://github.com/elliotglazer/diophantine-z-q/pull/69#issuecomment-6869577863), [copy](run-43542130192-fable.md): both accept and each resolves all four findings. |

The four false-lemma finding IDs were `43540895723-1-astra-M1`,
`43540895723-1-fable-SMOKE-1`, `43540895723-1-fable-SMOKE-2`, and
`43540895723-1-fable-SMOKE-3`. The repaired-head reports disposition these IDs;
the override itself did not turn the false lemma into an accepted argument.

## Override execution evidence

| Override run | App check and retained output | Review-step duration | Result |
|---|---|---|---|
| `43541667649` | [132283452940](https://github.com/elliotglazer/diophantine-z-q/runs/132283452940), [copy](check-132283452940.md) | 6 seconds | Failure: incomplete finding coverage. |
| `43541748780` | [132283724369](https://github.com/elliotglazer/diophantine-z-q/runs/132283724369), [copy](check-132283724369.md) | 5 seconds | Failure: incomplete finding coverage. |
| `43541776483` | [132283840296](https://github.com/elliotglazer/diophantine-z-q/runs/132283840296), [copy](check-132283840296.md) | 5 seconds | Failure: incomplete finding coverage. |
| `43541825778` | [132283952957](https://github.com/elliotglazer/diophantine-z-q/runs/132283952957), [copy](check-132283952957.md) | 9 seconds | Success: all four overrides; output names `elliotglazer` and marks affected claims **NOT outside reviewed**. |

The [historical override branch](https://github.com/elliotglazer/diophantine-z-q/blob/fd7aa392eb9ba630aed733486f6252305610fea8/.github/workflows/protocol-b.yml#L791-L800)
used by these runs consumes the App's stored decisions and does not call either
model. The Jobs API supplies the step timestamps copied in `live-tests.md`.
The implementing agent's downloaded run artifacts contained no model-turn
records for these four runs. Together these support the operator's observation
of zero new model calls. Duration alone would not establish this, and provider
billing records were not independently inspected. There are no new reviewer
reports for override runs: their source judgments are the completed false-lemma
reports linked above.

## Review history and remaining limits

[Pre-activation reviews](../pre-activation-reviews.md) preserve original files
where available and label owner-reported review history where they are not.
PR88 merged by owner bypass, not App acceptance. At this snapshot, PR87 is
still the protected live activation test; its merge and post-merge workflow
behavior have not yet been observed.

The owner deferred interruption, unauthorized-override and real `pause_turn`
tests. A branch/tag secret-access denial test was not run. App-pin readback
was performed instead of a deliberate forged-check merge attempt. None of
these unrun cases is represented as a passed test.

The six findings from [PR87's Astra report](https://github.com/elliotglazer/diophantine-z-q/pull/87#issuecomment-6870447889)
and [Fable report](https://github.com/elliotglazer/diophantine-z-q/pull/87#issuecomment-6870460493)
remain for both reviewers to disposition on the repaired head:

| Earlier finding | Repair submitted for review |
|---|---|
| `43547743436-1-astra-INC1` | Current contributor, agent and Lean policy documents now point to active Protocol B. |
| `43547743436-1-astra-DEP1` | Settings claims name the operator, observation time and verification limits, with a nonsecret API snapshot. |
| `43547743436-1-astra-TEST1` | Exact App outputs and published reports accompany all selected tests and all four override runs. |
| `43547743436-1-fable-stale-entry-docs` | The two root entry documents no longer describe the review protocol as unimplemented. |
| `43547743436-1-fable-activation-preconditions` | Outside-family review remains required; its history is recorded with provenance limits, and untested activation checks are explicit. |
| `43547743436-1-fable-live-test-record` | Correct-lemma row added; App/report links, override evidence and explicit PST/UTC dating supplied. |

This table describes proposed repairs. It does not supply reviewer dispositions
or authorize an override of any finding.
