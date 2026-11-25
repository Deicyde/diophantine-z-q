# Cai–Chen–Liu retirement verification

## Base

```text
git fetch origin wip/ccl-retire3
  exit 128: CONNECT tunnel failed, response 403
git -c http.proxy= -c http.lowSpeedLimit=1 -c http.lowSpeedTime=15 fetch origin wip/ccl-retire3
  exit 128: Could not resolve the origin host
git branch --show-current
  wip/ccl-retire4
git rev-parse HEAD refs/remotes/origin/wip/ccl-retire3 refs/remotes/origin/main
  f5299bb9d6f9ada2fcd170099f784f0e0945bf79
  f5299bb9d6f9ada2fcd170099f784f0e0945bf79
  29bfbc3f6793d98b7c1ac637f9728fe51e701e5b
git log --stat -2 f5299bb9d6f9ada2fcd170099f784f0e0945bf79
  f5299bb9d6f9ada2fcd170099f784f0e0945bf79
  7a6fe452cb6928367be04bb261e84e1506e9c078
git show -s --format='%H %P' e1dc7927406401baf9e4300fe46905428751c51d
  e1dc7927406401baf9e4300fe46905428751c51d 5eb9d5d33bba7f12155eb964c487c206ee1ed0cf 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b
```

## Builds and axioms

```text
awk '/^PASS / {print $2}' scratch/ccl-retire2/builds.txt
  25 Lake targets and scratch/ccl-retire/Check.lean
git diff --no-renames --name-status 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b f5299bb9d6f9ada2fcd170099f784f0e0945bf79 -- '*.lean'
  21 modified, 2 added, 3 deleted
git ls-files --error-unmatch -- <module path>
  All 47 deduplicated Lake targets resolved, including all nine downstream modules.
git ls-files --error-unmatch -- scratch/ccl-retire/Check.lean
  scratch/ccl-retire/Check.lean
uptime
free -g
  Before every run, one-minute load <= 120 and available memory >= 20 GiB.
  Initial guard dry run: awk rejected the load variable name before starting Lake.
  Guard corrected and checked before restarting.
systemd-run --user --quiet --wait --pipe -p MemoryMax=60G
  memory.max = 64424509440 bytes; flock serializes the compiler subprocesses.
lake --no-ansi --fail-fast build <module>
  47 passed; see builds.txt.
  Lake logs record re-elaboration of all nine downstream modules.
lake --no-ansi env lean scratch/ccl-retire/Check.lean
  All three direct imports built first; 21 declarations checked.
  Axioms: propext, Classical.choice, Quot.sound. See axioms.txt.
diff -u scratch/ccl-retire2/axioms.txt scratch/ccl-retire4/axioms.txt
  exit 0
```

## Import closure and count

```text
git ls-files -- ZInQKernel.lean ZInQKernel CMSerreTateSupport
  .lean paths indexed as project modules; CMSerreTateSupport/ stripped from module names.
git diff --no-renames --name-only 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b f5299bb9d6f9ada2fcd170099f784f0e0945bf79 -- '*.lean'
  Exclusion set; pinned main headers substituted for changed paths on the main pass.
Python: header imports only, skipping nested regular comments and line comments;
        closure() from scratch/ccl-unit-index2/closure.py, as in scratch/ccl-retire2/log.md.
29bfbc3f6793d98b7c1ac637f9728fe51e701e5b
  ZInQKernel.OneProof.Main (10587 project modules including root)
    changed or deleted modules: none
  ZInQKernel.Contrib.OneProof.SelmerTwoPower (380 project modules including root)
    changed or deleted modules: none
f5299bb9d6f9ada2fcd170099f784f0e0945bf79
  ZInQKernel.OneProof.Main (10587 project modules including root)
    changed or deleted modules: none
  ZInQKernel.Contrib.OneProof.SelmerTwoPower (380 project modules including root)
    changed or deleted modules: none
Project-module sets equal between main and retirement for both roots.
Exclusion set: 26 changed or deleted Lean paths.
The nine downstream closures include H20HeegnerNorm on pinned main and exclude it on the retirement tree.
git grep -n -F '(hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)' -- ZInQKernel/OneProof/Main.lean
  ZInQKernel/OneProof/Main.lean:269
git diff --exit-code 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b f5299bb9d6f9ada2fcd170099f784f0e0945bf79 -- ZInQKernel/OneProof/Main.lean docs/one-proof/kinds.tsv docs/one-proof/claims.tsv docs/one-proof/OPEN.md
  exit 0
  H hypotheses: 21, strict 4 published / 17 GLUE.
  Removed frozenTarget fields / GLUE rows / LEAF rows: 0 / 0 / 0.
```

## Retired names

```text
git grep -n -w -E 'CCLThm2_15Applied|CCLGenuine|H20HeegnerNorm|CommonCoordinate18E2|CommonCoordinate18LeafE2|CommonCoordinateInputsGenuineE2|E2ChainInputs|HeegnerTransportAt|hnorm_of_print_on|hnorm_of_genuine_print|commonCoordinateTarget_of_genuineE2' f5299bb9d6f9ada2fcd170099f784f0e0945bf79 -- '*.lean' ':!scratch'
  exit 1: no matches
```
