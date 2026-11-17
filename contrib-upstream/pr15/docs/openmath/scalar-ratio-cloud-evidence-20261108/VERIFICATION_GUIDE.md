# Evidence for the completed 39-target Lean comparator run

**Verification status: PASS for the frozen conditional algebraic packet.** This
is an evidence-only branch. It does not merge into the base automatically and
does not assert that the arithmetic Selmer/Poitou–Tate bridge is proved.

## 1. Identity and exact invocation

- Repository cloned for execution: `https://github.com/CheyLoveday/diophantine-z-q.git`
- Branch cloned for execution: `codex/derivative-switch-boundary-v13`
- **Execution checkout:** `e653d6ff295ae4e0535710a7d64aa255d294d211`
- **Reviewed mathematical source:** `3d2243ff141f9681fbd6a659ca28ffddfae9b000`
- Expected generated-project manifest SHA-256:
  `117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`
- Original research packet manifest SHA-256:
  `d313ec3ff5ad0e91d555d26b2beef6ad401d7e9c86cdfe77adbe119062498610`

The execution checkout and the earlier reviewed mathematical source are
separate identities, as required. The actual invocation was made inside the
fresh generated project `lean/.checks/openmath-scalar-ratio`, not the inherited
`ZInQ` target:

```sh
lake comparator --config comparator.json --paranoid
```

**Actual comparator exit code: `0`.** The raw invocation record, exact command,
working directories, and all other commands are in
[RESULT.json](RESULT.json) under `commands`.

The bundle contains 21 earlier targets plus 18 new targets, **39 selected target
names in total**. The original six are already contained in the 21; they are not
counted a second time. `definition_names` is empty. Only `propext`, `Quot.sound`,
and `Classical.choice` are permitted.

See the [checkout receipt](openmath-evidence-39/checkout.txt),
[preparation receipt](openmath-evidence-39/OPENMATH_PREPARATION.json), and
[full comparator configuration](openmath-evidence-39/comparator.json), which
contains the complete 39-name list and the permitted axioms.

## 2. Individual checker results

All six configured checks ran and accepted the solution. These are the exact
acceptance messages in the preserved stdout; no checker was skipped or treated
as unavailable.

| Checker | Actual result | Executable identity |
|---|---|---|
| Lean default | `Lean default kernel accepts the solution` | `leanchecker`, SHA-256 `12c38901cdbfab178f1bf6145dd30012e9a3b2c11ca695292a5884fa3cbaddb6` |
| Lean paranoid | `Lean paranoid kernel accepts the solution` | `leanchecker-paranoid`, SHA-256 `ca74d1e9a856149ed05acb600d8931a574dd9f465745beeaf93e3de7b7cbe274` |
| lean4lean | `checked 11492 declarations`; `lean4lean kernel accepts the solution` | `lean4lean`, SHA-256 `baaec030a70c78562ced2c75866ab0d2410e81ce680b835179ed16570ad5ef97` |
| nanoda | `nanoda kernel accepts the solution` | `nanoda_bin`, SHA-256 `cbf13950fc4a48f635a0beceeb5ed32dd82568b870cfd081b6391c1f2cf02ba5` |
| con-leche | `con-leche: accepted 11495 declarations (--verified)` | `con-leche`, SHA-256 `23a32522ea2c79f4ec8b48916272b37a423bda171e57cd83cfcf142eec50e621` |
| con-ron | `con-ron: accepted 11495 declarations (--verified)` | `con-ron`, SHA-256 `60f4ca9fb9436c323789fa49aae33af6dcd1b9b54b43a66b461779ce79fd8eec` |

Executables resolve under the recorded Lean prefix
`/opt/lean.4.35.0-56a005855ea1` on this VM. Individual external binaries are
identified by path and binary hash; no unreported alternate external version
numbers are inferred. [checker-identities.json](checker-identities.json) holds
the exact per-checker records and acceptance strings.

## 3. Toolchain, platform and dependencies

- Lean:
  `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`
- Lake: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`
- Bubblewrap: **0.11.1**; independent `--unshare-all --die-with-parent --ro-bind`
  probe exited **0**.
- Linux platform: see [platform.txt](openmath-evidence-39/platform.txt).
- Dependency cache: official Mathlib master-cache command listed in
  [the execution record](RESULT.json), with actual cache log under
  [dependency-cache.log](openmath-evidence-39/dependency-cache.log).
- All **nine** locked dependency revisions matched installed revisions and had
  clean tracked source. [dependencies.json](openmath-evidence-39/dependencies.json)
  contains each expected revision, actual revision, clean-tracked-source check and
  status. The received [lake-manifest.json](openmath-evidence-39/lake-manifest.json)
  preserves the original pins, and [lean-toolchain](openmath-evidence-39/lean-toolchain)
  preserves the compiler request.

No dependency was upgraded or removed to obtain a passing result, and no checker
or sandbox was bypassed.

## 4. Hash preservation and intentional holes

The generated project manifest has **24 signed input files**, so including
`MANIFEST.sha256` gives **25 source files**. The additional
`OPENMATH_PREPARATION.json` is an unsigned receipt, not a 26th source input.

The following preserve the actual before/after checks, including which files
were unchanged:

| Point in execution | Log | Exit code |
|---|---|---|
| Before dependency acquisition | [manifest-before.log](openmath-evidence-39/manifest-before.log) | 0 |
| After dependency acquisition | [manifest-after-cache.log](openmath-evidence-39/manifest-after-cache.log) | 0 |
| After the protected comparator | [manifest-after-comparator.log](openmath-evidence-39/manifest-after-comparator.log) | 0 |

The actual manifest is [MANIFEST.sha256](openmath-evidence-39/MANIFEST.sha256).
The research-packet manifest is
[research-packet-MANIFEST.sha256](openmath-evidence-39/research-packet-MANIFEST.sha256).

All **39 intentional Challenge proof holes** appear exactly once.
`sorryAx` is forbidden in solution proofs. The solution emits no `sorry`
warning. The raw non-module and three unused-DecidableEq warnings are retained;
no linter was disabled or result filtered. For the exact warning locations see
[challenge-warning-inventory.json](openmath-evidence-39/challenge-warning-inventory.json).

The protected replay's `Building Solution`, `Exporting`, and `Running ... kernel`
stages are all in [comparator.stdout.log](openmath-evidence-39/comparator.stdout.log).
[comparator.stderr.log](openmath-evidence-39/comparator.stderr.log) is the
untouched **empty** captured stderr file.

## 5. Exports and retained compiled artifacts

The comparator exports an environment for each of Challenge and Solution, using
Lean's scoped temporary-file mechanism. The documented `IO.FS.withTempFile`
deletes that NDJSON stream after use. **No retained standalone NDJSON export is
claimed or available here.** This is not a claimed checker failure.

What **is retained** is the complete set of 24 compiled `.olean`, `.ilean`, and
`.trace` artifacts for the seven solution research modules plus `Solution`.
They are under [compiled-artifacts](compiled-artifacts), with each byte count,
relative source path and SHA-256 in the `proof_export.compiled_artifacts_retained`
array in [RESULT.json](RESULT.json). These compiled files are not relabeled as
the temporary stream consumed by the kernel checks.

No alternative or reconstructed export was substituted for the captured proof
checking, and no knowledge-base claim is inferred from those artifacts alone.

## 6. Readable evidence map

- **Archive and SHA-256:** [openmath-39-verification-e653d6f.zip](openmath-39-verification-e653d6f.zip),
  SHA-256 `99105c6d1bd13ffaad86e9917edc533ac223ff115e833b165e409b3e17c73f2d`.
- **This repository's full execution receipt:** [RESULT.json](RESULT.json).
- **Original archive-content manifest:**
  [EVIDENCE_MANIFEST.sha256](EVIDENCE_MANIFEST.sha256), SHA-256
  `98db83730cf6a5df5bfa50afd055be72affb6d6d2ae59b8b92a018a89fdfac9f`.
- **Execution summary from the completed run:**
  [README.md](README.md).
- **Required repository instructions and source-facing scope:**
  [required-reading](required-reading).
- **Complete standard tool identities and hashes:**
  [checker-identities.json](checker-identities.json).
- **Preparation process:** [preparation.log](openmath-evidence-39/preparation.log),
  preserving the offline generation status and the separate recorded native
  execution steps that preceded the protected replay.
- **Sandbox execution probe:** [sandbox-probe.log](openmath-evidence-39/sandbox-probe.log)
  and [sandbox-probe.exit-code.txt](openmath-evidence-39/sandbox-probe.exit-code.txt).
- **Final checkout status:** [final-repository-status.txt](openmath-evidence-39/final-repository-status.txt).

The [PR_INDEX.sha256](PR_INDEX.sha256) file contains a SHA-256 manifest of this
whole documentation/evidence directory, including the new guide itself.
`MANIFEST.sha256` and the original `EVIDENCE_MANIFEST.sha256` were copied
unchanged; `PR_INDEX.sha256` was the only manifest newly generated for this PR.

## 7. Limits and arithmetic scope

No requested checker was unavailable or not run. There were no timeout,
resource, dependency, or sandbox failures. The protected replay was performed
in this VM under Linux bubblewrap, rather than being asserted as an independent
review or an Open Math cloud execution.

A compiler and an axiom-checking comparator certify the specified algebraic
statements under the stated frozen trust base. They do **not** establish human
arithmetic acceptance. In particular, the actual arithmetic Selmer presentation,
Poitou–Tate boundary–cup compatibility, cross-boundary normalization,
restricted converse, limit persistence, and the main Diophantine theorem remain
**OPEN** and are not part of this evidence-only branch. The arithmetic bridge and
this evidence delivery are deliberately separate.

The archive and this guide are offered to support review of upstream draft PR
[#15](https://github.com/elliotglazer/diophantine-z-q/pull/15), not to imply that
this evidence-only branch has itself been merged.
