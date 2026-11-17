# Hosted kernel capacity

The required kernel job has a 360-minute limit on the existing Ubuntu hosted
runner. It requests an additional 24 GiB swap file, preserving any existing
swap. This is a capacity increase, not a change to the declarations replayed or
the exact-target checks. Build workers remain at four and audit workers at one.

After fetching dependencies, the job checks the filesystem holding
`RUNNER_TEMP`. It allocates the file only with at least 28 GiB free, leaving
4 GiB of disk headroom. With less space it warns, records that the additional
allocation was skipped, and continues with existing swap. It never reports
that 24 GiB is active merely because it was requested. The diagnostic reads
`/proc/swaps`, verifies the exact new file and its usable size, and preserves
the requested and actual capacities in `kernel-swap-<attempt>`. A failed
allocation or a false claim of activation still fails the step.

The secret-free review preflight may wait 355 minutes for the same kernel run,
inside its own 360-minute job limit. Setup, queueing or a kernel run near the
six-hour limit can outlast this waiter. In that case no paid review starts;
the dispatch claim remains recorded. A later review command reconciles that
existing run before doing anything else. It does not dispatch a duplicate.

The first measured PR151 run, `44048587166`, had about 63.75 GiB free after its
old 8 GiB allocation. Its cold root build took 57m53s. The timing tool reported
11.61 GiB maximum resident set size, which is not a sum of simultaneously
running processes. The sampled process-tree and host-memory records provide
the complementary measurements. The full audit passed in 22m02.927s, with maximum RSS 14.13 GiB.
Its report covered all 944 project modules and 37,708 declarations. This observation supports trying the larger
swap allocation; it does not guarantee disk capacity on every hosted runner.

Verified reuse of main's outputs, chained build jobs and an audit split into
pieces are separate work. This change does not restore project caches on PRs
or non-main direct executions. The complete formalization remains in this
repository on main.
