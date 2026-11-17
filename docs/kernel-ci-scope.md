# When the required kernel job can skip its build

`Complete kernel build and exact-target audit` reports on every pull request.
There is no trigger path filter. Its first step obtains the complete paginated
PR file list, binds it to the event's base and head commits, and rechecks those
commits after classification. Renames include both names. Only an explicit
successful `full_build=false` result skips subsequent steps, including checkout,
Lean installation and artifact upload. A failed classifier step runs the build.
Pushes to main and manual runs always build.

The first step embeds `scripts/kernel_pr_scope.py`; it does not check out or
execute a PR's copy of that script. The offline test checks that the embedded
source and the maintained source match.

## Input inventory

| Consumer | Inputs that require the full build |
| --- | --- |
| `check_kernel_contract.py:validate` | `KERNEL_CONTRACT.json`, every path pinned in either the base or head contract, every tracked `.lean` file anywhere, and every `lakefile.lean` or `lakefile.toml`. The global Lean-file rule is necessary because the bypass-option scan is not limited to kernel modules. |
| `check_kernel_contract.py:lean_modules` | `ZInQKernel.lean`, `ZInQKernel/**`, `ThirdParty/GreenTao/**`, `lean/ZInQ.lean`, `lean/ZInQ/**`. The classifier covers all of `ThirdParty/**` and `lean/**`. |
| `check_kernel.py` and Lake | The root and nested `lake-manifest.json`, `lakefile.toml`, `lakefile.lean` and `lean-toolchain`; all sources above; the local `lean/` package; pinned dependency revisions; `scripts/check_kernel_contract.py`, `scripts/check_target.py`, `scripts/audit_kernel.lean`; and `build/kernel-ci/**`. |
| `check_target.py` | `lean/Frozen/BoundedIntegerPolynomial.lean` and `ZInQKernel/Target.lean`. |
| `kernel_base_report.py` | The base commit's `KERNEL_CONTRACT.json`, `.github/workflows/kernel-lean.yml`, authenticated main-push `kernel-audit` artifacts and generated `build/kernel-ci/base-*.json`. External artifacts are not PR files; main pushes still always build. |
| `test_kernel_contract.py` | `check_kernel_contract.py` and its inline temporary repository fixtures. |
| `test_kernel_audit.py` | `scripts/audit_kernel.lean`, `lean-toolchain`, the pinned Lean executable and inline temporary Lean fixtures. |
| Workflow, checkout and caching | `.github/workflows/kernel-lean.yml`, `.gitattributes`, `.gitmodules`, `.lake/**`, the root and nested toolchain/manifests, and all `scripts/**`, including every `scripts/*kernel*` file and the new classifier/tests. |

Unknown paths also build. Skip candidates are `.md`, `.tex`, `.bib` and `.pdf`
documentation outside protected locations; the independent Protocol B workflow,
reviewer instructions and `tests/protocol_b/*.py` files; and these Research-only
inputs:

- Under `research/versionNN/`, where NN is a positive decimal integer without
  leading zeroes: `.json`, `.py`, `.txt`, `.csv`, `.tsv`, `LICENSE` and `NOTICE`.
- Exactly `docs/current-manuscript.json` and
  `docs/audit-history/builder-binding.json`.

The versioned files hold polynomial tables, standalone verifiers, reports and
notices. The two release records select the manuscript and bind its builder
review. Research checks consume them. The kernel workflow, Lake configuration,
`check_kernel.py`, `check_kernel_contract.py`, `kernel_base_report.py`,
`check_target.py`, diagnostics and kernel tests do not read these files. The
kernel contract's global scan still reads any `.lean` file or Lake configuration
inside these directories; those always require the full build.

Membership in either the base or head contract takes precedence over every
exemption. All existing Lean, toolchain, configuration and protected-path rules
also take precedence. Renames still test both paths. Unknown formats, including
archives and shell scripts, still build. Other files under `.github/`, `tests/`
or `build/` still build. This changes only whether the kernel job needs to build;
it does not skip Research checks or mathematical review of the construction.

An unavailable or malformed contract, API failure, changed PR revision,
missing/duplicate file rows, unknown change status or a diff exceeding GitHub's
3,000-file API limit requests the full build. This is deliberately conservative.

## Validation and review

Run `python -B scripts/test_kernel_pr_scope.py -v`. The tests demonstrate that
`docs/guide.md` skips and `ZInQKernel/Contrib/Proof.lean` builds, and cover pinned
documents, all current contract entries, renames, pagination, unknown files,
incomplete lists, revision changes, API failures, push/manual runs and the
unchanged required job name. They also cover versioned data/verifiers, pinned
exceptions, nested Lean/configuration files and renames out of `scripts/`.
The skip writes its reason to the step summary.

This change updates the workflow and line-ending rules' contract hashes and
adds the classifier and its tests to the contract; it does not change mathematical targets or Lean
sources. Jack McCarthy (`Deicyde`) is being asked to confirm this inventory, and
Fable will review the follow-up PR before merge. Neither confirmation is
claimed by these offline tests.
