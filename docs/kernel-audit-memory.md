# Kernel audit memory investigation

The November 13, 2026 failures reached the audit preparation stage after a successful
Lake build and frozen-target check. Exit 143 reports termination, not a Lean proof
failure and not, by itself, proof of an out-of-memory kill.

| Run | Last frozen-target line (UTC) | Outcome |
|---|---|---|
| [43527139827](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43527139827) | 23:31:53 | runner shutdown at 23:36:18 |
| [43527559226](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43527559226) | 23:35:30 | runner shutdown at 23:39:13 |
| [43524572231](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43524572231) | 23:12:17 | audit passed at 23:28:08; 923 modules, 36,347 declarations |
| [43530684015](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43530684015) | November 14, 00:07:01 | audit passed at 00:26:17; 969 modules, 39,267 declarations |

All four restored the same project cache, ending in
`68197d94c7f4ce1261fdbad1158c8a9d696a8be8`. A warm cache does not skip the audit.
The longer failed run 43528557188 attempt 1 was also reported to stop after the
frozen-target check; its downloaded job log was incomplete at investigation time.
Do not infer its internal audit phase from that incomplete log.

## Minimal mitigation and measurement

The hosted Linux job adds **8 GiB of swap** before the build/audit step, preserving
existing swap and leaving another 4 GiB of free disk headroom. If less than 12 GiB
is free, it warns and continues the full audit without additional swap. Only the disposable runner is changed; no repository
secret or persistent host setting is involved. VM teardown removes the swap file.

The audit prints and flushes phase boundaries: project import, serialized body
scan, external-base import, kernel replay, duplicate-body checks, axiom closure,
and exact target checks. The upstream replay invocation is unchanged. Lean 4.35's
`Lean/Replay.lean` traverses the replay set serially; `LEAN_NUM_THREADS=4` does not
turn that loop into four simultaneous replays.

`check_kernel.py` samples the audit process tree and host memory every five seconds,
prints a heartbeat every thirty seconds, and flushes samples to
`build/kernel-ci/kernel-audit-memory.jsonl`. Where cgroup v2 exposes them, samples
include its limit, current usage, peak, swap usage and OOM event counters. These
are job-group measurements, not necessarily measurements of the auditor alone.
Process RSS sums are sampled, may double-count shared pages, and are not PSS.
Missing metrics are unknown, not zero.

On Linux, GNU `time -v` additionally records OS-reported maximum resident set size,
CPU time, page faults and exit status in `kernel-audit-resource-usage.txt`. Its
maximum RSS is a process high-water measure, not simultaneous aggregate process-tree
memory. It is printed at completion. A forcibly lost VM may not preserve the final
report; flushed heartbeat lines are the fallback evidence. The existing artifact
upload retains the logs when the runner survives.

There is no reduced module set, omitted duplicate check, extra admitted axiom,
changed exact target, or relaxed failure status. The source contract is updated
only for the workflow and diagnostic implementation changes and their tests.

## Separate follow-up options for Jack

The auditor presently runs with `lean --run`, imports the full project, keeps that
environment while importing an external-only base, and replays project declarations
into the base. This can retain substantial data, but peak memory and its phase
must be measured before attributing these failures to a particular allocation.

1. A compiled standalone auditor could reduce interpreter overhead. Compile only
   the trusted auditor, preserve data-only candidate imports (no candidate native
   initializers), and compare peak memory and wall time on identical inputs.
2. Reduce overlapping environment lifetimes, after identifying every use of the
   original environment. The raw duplicate bodies, full axiom dependency closure,
   external-base isolation and exact target checks must remain available. Simply
   dropping one import or trusting merged declarations is not equivalent.

Neither redesign is part of the swap patch. Evaluate with the same source/toolchain,
module set and cache, and retain all adversarial kernel-audit tests. A passing run
with swap establishes successful execution, not by itself the historical root cause.
