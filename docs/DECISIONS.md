# Decisions

One line per decision: date, what was decided, and where (issue, pull request or comment). Newest first. A decision
that replaces an older one says so, and the older line stays.

- 2026-11-17: The reference text is the 5 November manuscript; the Lean deviates from it only when needed, and each
  deviation is documented. ([#95](https://github.com/Deicyde/diophantine-z-q/issues/95), [#97](https://github.com/Deicyde/diophantine-z-q/pull/97))
- 2026-11-17: The proof follows the manuscript's Section 5: the headline takes pole completeness (Theorem 5.2), and
  deriving it from the restricted converse (Theorem 5.3) is lane [#83](https://github.com/Deicyde/diophantine-z-q/issues/83).
  Route K (through Tian–Yuan–Zhang and Gross–Zagier) is retired and kept at the tag `route-k-final`.
  ([#74](https://github.com/Deicyde/diophantine-z-q/issues/74), [#3 landing note](https://github.com/Deicyde/diophantine-z-q/issues/3#issuecomment-6958654442))
- 2026-11-17: A row whose flag marks it unread or unverified counts GLUE in both columns until a reader has checked it
  against the printed page. (`scripts/one_proof/render_open.py`, docs/one-proof/STATEMENT-CHECKS.md)
- 2026-11-17: Outside pull requests get a static review; the project's machines build and run only the project's own
  code. ([#74, decision 2](https://github.com/Deicyde/diophantine-z-q/issues/74#issuecomment-6950868382))
- 2026-11-17: Files from outside contributors' upstream pull requests are kept, unbuilt, under `contrib-upstream/`.
  ([#71](https://github.com/Deicyde/diophantine-z-q/pull/71), [#73](https://github.com/Deicyde/diophantine-z-q/pull/73))
- 2026-11-17: Fork PR #84 is not merged as it stands (its Lean duplicates main); its blueprint wording landed with
  credit in #87 and #88. ([decision](https://github.com/Deicyde/diophantine-z-q/pull/84#issuecomment-6961421913))
- 2026-11-17: Process for parallel work: lanes with declared footprints, one writer per shared file (OWNERS.tsv), the
  push gate and the PR guard. ([docs/one-proof/LANES.md](one-proof/LANES.md))
