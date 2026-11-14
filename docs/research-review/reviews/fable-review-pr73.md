# Review of PR 73: swap and memory diagnostics for the kernel audit

Reviewer: Claude Fable 5.2, in Elliot's Claude Code session, November 13, 2026.

**This file was written after the merge, from the record of the review given to Elliot in conversation during the session. The findings and decisions below are the ones reported at the time; no new review was performed for this file.**

**Decision at the time: accepted for merge at commit `c8ce014f`.**

**Independence.** Independent of the code. I had identified the audit phase as the likely point of failure from the build log and from reading `scripts/check_kernel.py` and `scripts/audit_kernel.lean`, and suggested swap space and diagnostics as the smallest fix, so I was not independent of the approach.

## Sequence

1. **Commit `8e37c7d6`** (first version). Checked:
   - The change to `scripts/audit_kernel.lean` was 22 added lines of flushed progress output and no removed lines. The replay, duplicate-body checks, axiom closure and target checks were unchanged.
   - `scripts/kernel_diagnostics.py` only reads memory figures from the operating system; the audit's exit code still decides the result.
   - `KERNEL_CONTRACT.json` was re-pinned for the files the PR changes, as the contract's design requires.
   - I could not run its tests locally, because they need the full repository.
   - One change requested: the swap step exited with failure when less than 12 GiB of disk was free. I asked that it warn and continue without extra swap instead, so a disk shortage would not fail a required check.

2. **Commit `a15b23e6`.** Confirmed the requested change: the step now writes a warning and a step-summary line and continues the full audit without additional swap.

3. **Hosted run 43536944996 on `a15b23e6`** (reported by Astra; figures read from the PR, not measured by me): passed, with 13.56 GiB maximum resident memory, 13.98 GiB sampled peak, 4.65 to 5.51 GiB of swap used at peak, on a host with 15.61 GiB of memory and 11 GiB of swap after the step (3 GiB before). Audit time 14 minutes 19 seconds. I noted that this supports the memory-pressure explanation and does not prove what killed the earlier runs.

4. **Commit `c8ce014f`** (merge of `main` after PR 72 landed, resolving conflicts in `.gitattributes`, `.github/workflows/kernel-lean.yml` and `KERNEL_CONTRACT.json`). Checked against `main` at `fd7aa392`:
   - The swap step carries the same skip condition as the other build steps.
   - PR 72's skip logic is untouched, and the embedded copy of the scope script is identical to `scripts/kernel_pr_scope.py`.
   - Both PRs' additions are present in the contract file and `.gitattributes`.
   - The PR changes the same eight files as before and nothing in the review gate.

## Notes given at the time

- The swap is a stopgap. The audit's memory use will grow with the Lean development, so the headroom will shrink. The proper fix, a lighter auditor, was left to Jack McCarthy.
- The merge did not wait for Jack McCarthy's review; Elliot decided to proceed and to have him review afterwards.

## Not verified

- I did not run the kernel build or the audit.
- The memory figures are Astra's, from the hosted run's artifact.
