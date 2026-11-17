# The discharge check

The discharge check builds an outside contribution and runs a trusted reporter on it, to show which open
hypotheses of `ZInQ.OneProof.frozenTarget` it proves, what it still assumes and which axioms it uses
(`docs/one-proof/CONTRIBUTING.md` is the contract). It runs as the fork's workflow
`.github/workflows/contrib-discharges.yml` ("discharge check"); this directory holds its scripts.

The result is advisory for every file. Contributor code runs during the build and again when the reporter
imports it, with full rights on the runner, so it can forge the result whether or not the scan finds anything.
A pass says what the reporter printed, not that the file is safe or correct.

## What runs where

- **On GitHub's hosted runners**, for every pull request into `main` that touches
  `ZInQKernel/Contrib/OneProof/`: the whole check, in a fresh virtual machine that is discarded after the job, starting from the newest build of `main` in the Actions cache.
- **On project machines**: nothing from a pull request. Lean runs code while it elaborates a file: `#eval`,
  `run_cmd`, `initialize`, macros, custom elaborators and tactics all execute during `lake build`, with the
  rights of the user who runs the build. Project machines hold SSH keys, GitHub credentials and network access,
  so building a pull request there would hand those to its author. A maintainer may read a pull request there
  only as git objects (`scan_contrib.py`, below), never checking it out, building it or running Lean on it.

Merging is trust. Once merged, a file is built on project machines at every fold, so a file with build-time code
is not merged. The project's agents check every added file (this scan, then a read); no person reads every file.
The check does not replace that agent read.

## The flow

The workflow runs on `pull_request` into `main` with the paths filter `ZInQKernel/Contrib/OneProof/**`. GitHub
checks out the merge commit. `BASE` is that commit's first parent and `HEAD` the pull request's head SHA, passed
through an environment variable; the step fails, with no result, unless `HEAD` is the merge commit's second
parent.

1. **Scope gate**, on git objects, before anything is built. The step first restores this directory from
   `BASE`, so a pull request cannot change the scripts it is judged by, then runs `discharge_check.sh scope`,
   which runs `scan_contrib.py` on the diff between the merge base and `HEAD`. Every changed path must be a new
   file under `ZInQKernel/Contrib/OneProof/`: Lean files, or plain-text files such as LICENSE, NOTICE or
   README.md in a helper directory there. A modification, deletion, rename, mode change, symlink, submodule or
   any path outside makes the pull request out of scope: nothing is built, the job fails, and the job summary
   says that the automatic check covers only pull requests that add new files under
   `ZInQKernel/Contrib/OneProof/` and change nothing else. In scope, the step writes `.sandbox/manifest.json`
   (base, head, added files). For an in-scope pull request the checkout is therefore `BASE`'s tree plus the
   added files, and every script and OneProof module in it comes from `BASE`.
2. **Scan** (advisory), in the same step; its log shows the scan as it stood before anything was built. Each
   added Lean file is searched for build-time code: every `#` command except `#check` and `#print`; commands
   starting with `run_`, `syntax`, `macro`, `macro_rules`, `elab`, `elab_rules`, `notation`, `infix`, `prefix`,
   `postfix`, `initialize`, `builtin_initialize` and their variants; attributes that register elaborators,
   macros, tactics, delaborators, formatters, parenthesizers, compiler passes, linters or native code; the
   words `axiom`, `by_elab`, `tactic`, `native_decide`, `ofReduceBool` and `implemented_by`, and any name
   starting with `unsafe`; and every escaped identifier (a name in guillemets). A hit is "likely" when it lies
   outside comments and strings as the scanner's lexer reads them, and "possible" when it is only in the raw
   text, so a disagreement with Lean's lexer can add hits but never hide one. An unterminated string, comment,
   escaped identifier or interpolation brace is a hit. Matching uses Lean's identifier characters and errs
   towards false positives. `import Lean` is only a note, since Mathlib re-exports Lean.
3. **Build**, in its own step, after `lake exe cache get` (Mathlib) and a restore of the newest build of `main` that `.github/workflows/main-build-cache.yml` saved, so only the contribution and what it changes are compiled. The step before the build fails the check if a run of the same pull request saved a build cache of its own.
   `discharge_check.sh build` builds `+ZInQKernel.OneProof.Main`, `+ZInQKernel.OneProof.Discharges` and each
   added module, and stops the build after 270 minutes. The nonce does not exist yet.
4. **Reporter**, in a separate step. The step makes `DISCHARGE_NONCE` with Python's `secrets` module; only
   this step's environment holds it. `discharge_check.sh report` runs `#discharges` from a generated
   `.sandbox/Check.lean` for the log (display only; the nonce is removed from that run's environment, but its
   imported code can still read it from the parent process), then the trusted reporter
   `DischargesJson.lean` through a generated `.sandbox/Report.lean`. The reporter repeats the matching of
   `#discharges` and prints one `DISCHARGE-JSON <nonce> <json>` line per discharging theorem and a summary line,
   with names inside JSON strings, so no name can break a line. `discharges_log.py` reads only lines with this
   run's nonce and rejects malformed records and names with control characters; it also reads the build log
   for errors and for Lean's sorry warning on the added files, and writes `.sandbox/out/result.json`. The
   verdict is fail on a build error, on any reported theorem that uses `sorry`, on any axiom beyond `propext`,
   `Classical.choice` and `Quot.sound`, on a rejected reporter line, on a reported theorem that assumes the
   hypothesis it proves (the reporter lists the open hypotheses each theorem's own hypotheses match), or when
   no theorem discharges an open hypothesis; a fail fails the step and the job. `render_open.py --check` runs
   too, but only as information: it checks the base commit's documents, not the contribution.
5. **Summary.** `discharge_comment.py` writes the verdict and the records as Markdown to the job summary (see
   below). The base and head it prints come from the scope step's `scan.json`; a `result.json` without the
   expected shape counts as no result. The job then uploads `.sandbox/out` (the logs, `scan.json` and
   `result.json`) as the artifact `discharge-check`.

## Security model

- The job runs on a GitHub-hosted runner: a fresh virtual machine per job, with no access to project machines. Its only state from earlier runs is the build of `main` restored from the Actions cache, which only pushes to `main` write (`main-build-cache.yml`); a cache saved under the pull request's own ref is refused.
- The workflow's only permission is `contents: read`, so its `GITHUB_TOKEN` can only read, and checkout runs
  with `persist-credentials: false`, so the token is not left in `.git/config`.
- The workflow uses no secrets, variables or environments. A pull request from a fork gets no secrets and a
  read-only token in any case.
- Whether an outside contributor's run waits for a maintainer's approval depends on the repository setting
  under Settings > Actions > General, which this workflow does not set and nobody has checked yet. It should be
  "Require approval for all external contributors": the first-time options stop asking once a contributor has
  had a commit merged. Nothing in the workflow caps how many pull requests run at once, since each has its own
  concurrency group. Approving lets the build run on a hosted runner; it does not make the file trusted.
- The trigger is `pull_request`, never `pull_request_target`, which would run with the base repository's
  secrets and a write token.
- No field of the event that a contributor controls (title, body, branch names, file names) is interpolated into
  a script; the scripts get only the head SHA, through an environment variable, and the merge commit's
  parents from git.

## Limits

- The result is advisory for every file, with or without scan hits. Contributor code runs at build time, and
  again, through `initialize`, when the reporter imports it, with the runner user's rights (hosted runners
  allow `sudo`). It can rewrite the reporter, the parser, the toolchain, `result.json`, the job summary or the
  artifact, and code that runs when the reporter imports the contribution can read the nonce. The nonce and the
  JSON format stop a crafted theorem name or a line printed during the build from passing as a record; they do
  not stop code that takes over the runner.
- The scan flags build-time code, and a file with scan hits is not merged. A clean scan lowers the chance of build-time
  code but does not rule it out; the scan matches tokens, not Lean's grammar, so it may flag harmless text, and
  a file can still do something it does not name. A file with scan hits gets "This file has scan hits: it may
  contain code that runs at build time. A file with scan hits is not merged, and this result does not count
  while it has them.", and the verdict headline says the same. A reviewer may ask for a lean4checker replay of
  the built oleans; that replay also runs on a hosted runner, since it loads the untrusted oleans.
- A pull request that edits the workflow, or anything outside `ZInQKernel/Contrib/OneProof/`, is out of scope,
  and its result does not count, whatever the check reports. On `pull_request`, GitHub runs the workflow file
  from the merge commit, so a pull request that edits `.github/workflows` can make the check print anything;
  restoring the scripts from `BASE` covers the scripts, not the workflow. Read the pull request's file list
  first.
- A run uses hosted runner time, and an outside file can make it long. The job limit is 300 minutes, a build
  stops after 270 and the reporter step after 20; no cold build of the OneProof target has finished on a hosted runner: before the build cache existed, five pull-request runs stopped at the 270-minute limit (see below).

## Reading the result

- The check covers only pull requests into `main`. A pull request into another branch, or one that changes
  nothing under `ZInQKernel/Contrib/OneProof/`, does not start the check at all.
- On the pull request, the check "discharge check" is listed with the others: green for pass, red for fail,
  out of scope, or a run that broke. A run that needs approval shows as waiting until a maintainer approves it.
- Its details link opens the run; the job summary holds the verdict headline, the base and head commits, each
  reported theorem with the hypotheses it discharges, what it still assumes and its axioms, the reasons for a
  fail, the build statistics and the scan hits. "No result" means the run wrote none; the run log says why.
- The artifact `discharge-check` holds the build log, the reporter's output, `scan.json` and `result.json`.
  Contributor code ran on the runner that wrote it, so treat it as contributor-controlled data (see Commands).

## The measurement run

A manual run (`workflow_dispatch`, from the Actions tab, on `main` or any branch) builds
`+ZInQKernel.OneProof.Main` cold, with only Mathlib from the cache and no contribution, so the build cost on a
hosted runner is known before the check is relied on. It runs `discharge_check.sh measure`, which builds under
`/usr/bin/time -v` with the 270-minute limit and writes `result.json` with the commit, the build's exit status
and whether it hit the limit, wall-clock seconds, the Lake job count, peak memory, and `df` and `free` before
and after. The job summary shows `result.json`, and the artifact holds it with the build log. Add the figure to
the build-cost table of `docs/one-proof/CONTRIBUTING.md`. The pull request check no longer builds cold: it starts
from the build of `main` that `main-build-cache.yml` makes after each push to `main` that changes Lean, never from
a contributor run or its cache.

## Commands

On a project machine, a pull request can be scanned as git objects only (nothing is checked out or built):

```
git fetch origin main "pull/<N>/head:refs/contrib/pr-<N>"
python3 scripts/one_proof/sandbox/scan_contrib.py origin/main refs/contrib/pr-<N> --json scan-<N>.json
```

`scan_contrib.py` exits 0 in scope, 2 out of scope and 1 on error. `discharge_comment.py --scan scan.json
[--result result.json]` formats a summary from a downloaded artifact. `python3 scripts/one_proof/sandbox/discharges_log.py LOG`
prints a `#discharges` text log as JSON, for display only.

A downloaded artifact is contributor-controlled data: build-time code can write any file into it, including
`.lean` files. On a project machine, read its JSON and logs only with `python3 -I`, and never open, build or
elaborate a `.lean` file from it (an editor with the Lean extension elaborates a file when it opens it).

After any change to `DischargesJson.lean`, check it on a project machine against the base commit alone
(project code only, never a contribution); its own imports are enough:

```
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
DISCHARGE_NONCE=test lake env lean scripts/one_proof/sandbox/DischargesJson.lean
```

Tests (standard library only, no network, temporary git repositories):

```
python3 -I -m unittest discover -s scripts/one_proof/sandbox -p 'test_*.py'
```
