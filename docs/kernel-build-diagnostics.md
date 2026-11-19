# Kernel build and audit diagnostics

The required **Complete kernel build and exact-target audit** job keeps the
same source-contract validation, complete module build, frozen-target check,
kernel replay, duplicate-body checks, axiom closure and exact-target checks.
Compilation and the audit run in separate workflow steps. A successful build
alone is not a passed kernel audit.

The build step writes `build-complete.json` only after all module batches, the
frozen-target check, dependency checks and source-contract checks succeed. The
marker binds the Git head, contract digest, compiler and complete module list.
The audit step requires that same identity, rechecks the frozen target and
dependencies, and then runs the unchanged Lean auditor. Required CI never uses
the local `--skip-build` option. The marker is progress evidence within the job;
it is not an independent attestation or a substitute for a successful job and
the final `kernel-audit` artifact.

Both compilation and audit subprocesses record memory samples, elapsed time and
GNU time resource usage. Each phase has its own files. The `kernel-build-<attempt>`
artifact contains the build marker, swap status, samples and timing/resource
records, without compiled outputs or full compilation logs. It is uploaded
between the build and audit steps, including partial records after an ordinary
build failure. A runner lost during the audit therefore leaves the completed
build evidence. During both compilation and audit, an optional background observer uploads
resource chunks immediately and then every two minutes after the preceding
upload finishes. Each finalized artifact has a unique name
`kernel-progress-<attempt>-<sequence>` and is downloadable while the kernel
step is still running. Completed chunks remain if the runner later disappears.
An ordinary job ending asks for a final chunk. Existing swap, completed-build
and audit uploads still read the original files with their existing actions.

Chunks bind the run, attempt, event SHA, actual checkout SHA, capture time,
file byte ranges and hashes. Only named memory, timing, resource-usage, swap
and build-marker files are copied. Complete JSONL lines start at the last
confirmed offset. A failed or uncertain upload leaves that offset unchanged;
a later unique chunk may overlap it. Use byte ranges to avoid counting samples
twice. The 2 MiB per-file and 8 MiB per-chunk limits expose any remainder.
Partial chunks are not evidence of build completion or kernel acceptance.

The observer never launches or controls a kernel command. Both commands retain
their original workflow steps, arguments, environment and failure handling.
Installation or observer startup failure is nonfatal and explicitly reported
in the step summary. The observer uses only first-party code and Node built-ins.
Only its bounded upload child imports the exact locked GitHub artifact client;
installation scripts are disabled. Contract pins cover the action, its code,
tests and dependency lock. Upload children use the snapshot directory as their
working directory and workspace, receive only snapshot paths, and do not
receive workflow command-file paths. The first-party observer writes no source
or proof-status file. This confines the intended reads and writes, but is not
an operating-system sandbox for the client dependency, which runs as the job
user and remains part of the reviewed toolchain.

Uploads are serial with one transfer worker, a 45-second deadline and a maximum
of 200 per job. They expire after 14 days. Temporary copies are removed after
each attempt; original diagnostics remain. Upload errors cannot replace a
kernel result. The stop step records whether any upload was confirmed in
`periodic-upload-status.json` and the summary. No workflow permission, secret,
proof check or resource setting changes. A runner or network failure can still
lose samples since the last confirmed upload. Step summaries alone would not
solve that problem because GitHub uploads them only after a step completes.

The swap step requests 24 GiB additional swap with a 28 GiB free-disk
threshold, leaving 4 GiB of headroom as described in
[Hosted kernel capacity](kernel-runner-capacity.md). It records the active devices reported by
`/proc/swaps`, their actual capacities and use, available disk space and host
memory. When allocation is attempted, the exact additional file must be active
at the requested usable size. If disk space is insufficient, the existing
warning remains and the record explicitly says `skipped-low-disk`; it does not
claim that 24 GiB was added. In that case existing active swap must still be
verified. No active swap, an absent/undersized newly allocated file, or an
unreadable verification record fails the step. Allocation command failures stay
failures even if recording succeeds.

Compilation defaults to `LEAN_NUM_THREADS=2` for Lake. The audit uses one worker
to reduce concurrent import/runtime memory demand. Its command passes `lean -j 1`
explicitly: the Lean 4.35 CLI does not take this limit from `LEAN_NUM_THREADS`.
The adversarial audit tests use the same explicit worker limit. The kernel replay was already
serial; this does not change what is replayed and is not a measured guarantee
of a lower peak. The hosted run must establish its actual memory use and runtime.
No proof statement, accepted axiom or cache policy changes. The capacity
change separately raises the job limit to six hours and the requested swap
allocation to 24 GiB.

Earlier runs set `LEAN_NUM_THREADS=4`, but that is not a measured count of
compiler or audit CLI workers. Compare the new explicit audit limit with the
previous CLI default, rather than treating that environment value as proof
that all earlier subprocesses used four workers.


On 17 November 2026, the [complete two-worker experiment](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44190746468)
passed on `6b79fa536870135935d6e58ea62c5dcb632d55dc`, with 24 GiB added swap.
Compilation took 40m50.401s. Its full audit agrees with the successful
four-worker baseline except for head and contract hashes. Root-build minimum
available host memory was 7.21 GiB versus 2.06 GiB, and sampled process-tree
swap peaked at 1.03 GiB versus 5.13 GiB. The runners differed, and the
baseline used `lake --rehash build` while the experiment used `lake build`.
This is one successful comparison, not a repeated-run reliability result.

The subsequent [two-worker PR164 run](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44201012447)
at `bd7cce201f1e8a283ebb637a850a389f22beddb1` retained main's older 8 GiB
additional-swap setting and lost its runner during compilation after 54m55s.
Its swap record confirms that allocation. No completed build marker, final
memory samples or audit survived. The lost-runner annotation does not prove
an out-of-memory failure. The combined configuration uses the authorized
24 GiB capacity with two build workers; subsequent runs must establish its
reliability. Memory sampling and complete audit coverage remain in place.

If this repair's hosted job fails, inspect the last completed workflow step,
the swap artifact, the build marker and any retained phase samples before
choosing another action. Do not infer OOM from "runner lost communication"
alone. If the runner disappears again, do not start a blind third attempt or
change resource settings in the same review cycle. Report the exact head, run,
phase evidence and missing evidence to the owner for the next measured repair.
