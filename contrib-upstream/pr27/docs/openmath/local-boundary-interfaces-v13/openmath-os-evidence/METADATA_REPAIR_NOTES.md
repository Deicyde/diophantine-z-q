# Metadata and operational repair notes

These are preservation notes for the independent PR #2 checking run. They are
not claims of mathematical bugs or fixes to mathematical proofs.

## Functional setup issues

1. The initial source-cache inventory could not find the `Cli` compiled package
   at the usual Lake cache path. The original runner correctly stopped at that
   missing input. The same pinned package source was then copied at revision
   `c24fe6078c630e89b489bffe59b3e20ac30d12c8` and built locally with success.
   A non-existent alternative standard-library cache path was not substituted,
   and no revision was upgraded.
2. Git's dubious-ownership guard objected to a root-owned installed Mathlib
   source. Only read-only revision/worktree inspection was permitted using
   `git -c safe.directory=*`; the global Git configuration and source content
   were not altered.
3. An interrupted checkout also left a zero-byte `plausible/.git/index.lock`.
   No active checkout process existed for that review-owned path, so only the
   stale lock was removed. Lake then reached the locked source revision and
   continued the selected build. The exact failed stderr and job log are in
   `initial-plausible-build.stderr.txt` and `initial-plausible-checkout-job.txt`.

The resulting native driver compile and axiom checks passed, and the prepared
project build did pass after these materialization steps.

## Timeouts and job-handling

The first background run exceeded a 25-second limit before export or any
checker invocation. A later implementation also reached an early Lake/package
checkout lock before obtaining a usable project. These were operational
timeouts rather than mathematical or kernel rejections. The genuine full
14-minute dependency/project rebuild and six-checker invocation was subsequently
given a 15-minute allowance and completed. The initial supervisor log is in
`initial-background-timeout.txt`; setup attempts are not represented as instant
successes.

## Evidence metadata helpers

After build/export and after the successful overall `lake check --paranoid`
process returned zero, a small series of newly written metadata
collectors/validators needed repairs. These did not occur inside Lean and did
not modify any proof, checker or export input.

- A metadata relative path was corrected to locate the evidence directory at
  the checkout root, rather than a nested `lean/docs` path.
- A mistaken check for an executable literally named `nanoda` was corrected to
  check the actual bundled executable `nanoda_bin`, which Lake had already used
  successfully. No new checker was fabricated or downloaded.
- Native compiled `Research` artifacts had to be read through their `lib/`
  intermediate path. The four actual `.olean` files were found there and copied
  into `core-artifacts/`.
- An indentation error in a newly written Python collector was corrected. It
  was rejected by the interpreter and never became a passing audit.
- An unnecessary `dict(argv)` conversion in the same helper was replaced with
  `list(argv)`.
- The validator was corrected for two non-mathematical output
  conventions: `sha256sum -c` emits independent `<input>: OK` lines rather than
  a synthetic `MANIFEST.sha256: OK`, and the raw text uses the exact count
  `19 + 8 + 7 + 7 = 41` and the heading `The 16 tested definitions`.
- The final prepared-dependency JSON initially omitted `cache_present`. Its
  compiled-cache directories were re-checked, and that accurate Boolean was
  inserted. No absence of a checker was permitted or hidden.

The earlier per-step raw stderr for these newly written helper fixes is not all
preserved as a separate immutable stream: the log files were overwritten on
retries and a successful final collector writes empty stderr. This note gives
the corresponding failure classes and the exact disposition without implying
that all of these transient attempts have their own independent full logs.

Both the final collector and validator exited zero. Their outputs, artifacts and
raw basic image digests were checked only afterwards. The final artifact ledger
has sixteen records plus the four copied module OLEANS and a hashed entry for
all actual used executable paths.

## Scope warning

The documented mathematical gaps are not part of these setup repairs. The local
conditional interfaces were checked without acquiring a proof of actual global
cup/trace normalization, stored-row/determinant-basis compatibility, continuous
Selmer objects or the main Diophantine theorem. All failures above are setup or
metadata operations, not claims against the source proof or its obligation map.

## Commit identity

Git could not create the evidence commit because no author was configured in
this VM. The evidence commit uses the explicitly automation-local identity
`Open Math OS Evidence <evidence@localhost>` through command-local `-c` options.
No repository-global or user-global Git configuration was changed, and this
identity is not being presented as the fork owner's identity or a human review.
