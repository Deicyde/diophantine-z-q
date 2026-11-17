# Local PR154 reviews

These files are preserved unchanged from Fable's local review and relay
messages. They are optional local reviews, not App-authenticated gate decisions.

- [Initial review](fable-review-pr154.md): the full review of `1e1224ac`,
  including the two blocking objections, notes, tests run and unread scope.
- [First repair follow-up](fable-repairs-read.md): Fable checked the narrowed
  automatic-merge category, but did not reread the queue repair line by line
  or rerun tests. It includes two further checks to make.
- [Round-one repair follow-up](fable-round1-repair-read.md): Fable read the
  workflow repair hunks, not the tests, and asked whether a wake could displace
  a queued collaborator command. The corresponding active/pending-command
  regressions are in `tests/protocol_b/test_outside_round_safety.py`.

The [first gate round](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44090851509)
raised three implementation findings and incomplete scope. In the
[second round](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44106033199)
at `b33f96befe73ed60575a3784d20858d875da5b60`, both reviewers marked the
three implementation findings resolved. Both still reported incomplete
scope. Fable raised the additional rollout-record finding
`44106033199-1-fable-L1-outside-lean-rollout`, also retained under its initial
invalid-delivery ID `44106033199-1-fable-unvalidated-1-1`.

The accompanying documentation repair links the completed
[controlled fork test](../fork-dispatch-2026-11-17/README.md), replaces the stale
pre-rollout restriction and supplies these previously unavailable local
reviews. It also distinguishes the first unattended attempt from subsequent
collaborator-requested rounds in the Light-profile explanation. These edits
do not declare the outstanding gate scope items or rollout finding accepted;
their disposition remains for re-review or an explicit admin decision.

The second round's nonblocking notes about an admission check masking a running
review, the bounded quota-scan capacity and editorial merge-command ordering
remain recorded in its original report. No repair of those three behaviors is
claimed by this documentation change. No live unattended admission test has
yet been performed.
