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
build evidence. A runner lost during compilation may leave no build artifact;
the separately uploaded `kernel-swap-<attempt>` artifact still records the
pre-build configuration if that upload completed.

The swap step retains the existing request for 8 GiB additional swap and the
12 GiB free-disk threshold. It records the active devices reported by
`/proc/swaps`, their actual capacities and use, available disk space and host
memory. When allocation is attempted, the exact additional file must be active
at the requested usable size. If disk space is insufficient, the existing
warning remains and the record explicitly says `skipped-low-disk`; it does not
claim that 8 GiB was added. In that case existing active swap must still be
verified. No active swap, an absent/undersized newly allocated file, or an
unreadable verification record fails the step. Allocation command failures stay
failures even if recording succeeds.

Compilation retains four Lean workers. The audit alone uses one worker to
reduce concurrent import/runtime memory demand. Its command passes `lean -j 1`
explicitly: the Lean 4.35 CLI does not take this limit from `LEAN_NUM_THREADS`.
The adversarial audit tests use the same explicit worker limit. The kernel replay was already
serial; this does not change what is replayed and is not a measured guarantee
of a lower peak. The hosted run must establish its actual memory use and runtime.
No proof statement, accepted axiom, memory capacity, cache policy or job timeout
is changed by this adjustment.

If this repair's hosted job fails, inspect the last completed workflow step,
the swap artifact, the build marker and any retained phase samples before
choosing another action. Do not infer OOM from "runner lost communication"
alone. If the runner disappears again, do not start a blind third attempt or
change resource settings in the same review cycle. Report the exact head, run,
phase evidence and missing evidence to the owner for the next measured repair.
