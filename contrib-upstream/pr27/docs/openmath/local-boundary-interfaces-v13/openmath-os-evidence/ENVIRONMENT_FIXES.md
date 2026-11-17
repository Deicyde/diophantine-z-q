Git wrapper for root-owned installed dependency trees (read-only metadata checks only):
exec /usr/bin/git -c safe.directory="*" "$@"

No proof or dependency source changed; no global Git configuration edited. The Cli package was separately rebuilt in the review workspace after its required cache was missing.

## Background-job timeouts

Job `jmwak0d7y` reached the repository job supervisor's 25-second limit while
`lake build` was still running and before an export or any checker invocation.
It was not a mathematical or checker failure. The recorded script is restarted
with a 15-minute limit; the earlier log is retained beside this note.

## Stale dependency checkout lock

The longer job then failed before export at `plausible/.git/index.lock`, left by
this review's interrupted initial fetch. No live Git process owned it. Only
that stale lock was removed; the checkout itself is allowed to finish at the
pinned revision. The complete failed stderr is retained as
`initial-plausible-build.stderr.txt`. This is still not a checker failure.
