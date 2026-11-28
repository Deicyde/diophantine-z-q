# Building and checking the research package

Run these commands from a clean checkout. Construction checks use Python 3.11 or later and Node.js 22 or later; the CI workflow pins Python 3.12.14 and Node.js 24.22.1. Python scripts use only the standard library.

## Construction

```sh
python scripts/check_construction.py --report build/construction-checks.json
```

This regenerates the rational expression from its pinned natural-polynomial input, checks hashes and wiring, recalculates syntactic bounds, and runs the supplied finite arithmetic checks. See [the construction README](../construction/README.md) for exactly what each check establishes. It does not prove the main mathematical theorem.

## 11/5 manuscript

```sh
python scripts/build_paper.py
```

The script downloads a SHA-256-verified Tectonic 0.17.0 binary for the host platform, then builds a copy of the 11/5 TeX source in an isolated temporary directory. It uses the fixed `tlextras-2022.0r0` bundle URL and checks the selected bundle's fingerprint. Tectonic fetches only the needed support files; it does not download the entire bundle archive. The first run requires network access. Later runs reuse the local resource cache.

If Tectonic 0.17.0 is already installed:

```sh
python scripts/build_paper.py --tectonic /path/to/tectonic
```

Results are written to `build/paper/`, including the compiled PDF, compiler log, TeX log, and a JSON receipt. The script fails on a compilation error, unresolved references or citations, or an unexpected bundle fingerprint. Typesetting warnings remain in the log.

The checked-in revision-2 PDF of the 11/5 manuscript, including the November 5 source-application audit repairs, was rebuilt from the corresponding TeX source. Its source and PDF hashes are recorded in [the current build receipt](theorem-application-audit/MANUSCRIPT_BUILD.json). Running this script creates a new build artifact without replacing the checked-in 11/5 PDF. Fixed engine, bundle, and timestamp inputs improve reproducibility, but this repository does not claim that PDF bytes are identical across operating systems.

## Lean helpers

Install [elan](https://github.com/leanprover/elan), then run:

```sh
cd lean
lake exe cache get
cd ..
python scripts/check_lean.py --build --output build/lean-local
```

The output directory must not already exist. The checked-in toolchain and Lake manifest pin Lean and Mathlib. The checker validates source hashes and dependency revisions, compiles the 48 accepted helper modules and their root into fresh project artifacts, and runs the axiom audit. Dependency binaries come from the pinned Mathlib cache and are not rebuilt by this command.

For the quick source and quarantine checks without compiling:

```sh
python scripts/check_lean.py
```

Read [the Lean README](../lean/README.md) for the trust boundary and allowed axioms. The main theorem remains unproved; its frozen `sorry` is excluded from the default imports and from the accepted-helper audit.

## Continuous integration

[Research checks](../.github/workflows/research-checks.yml) runs three separate jobs for construction, 11/5 manuscript compilation, and accepted Lean helpers. It runs on pushes to `main`, pull requests, and manual dispatch. GitHub Actions dependencies are pinned to commit hashes, and the elan installer and Tectonic archives are pinned by SHA-256. TeX resources are cached between runs. Each Lean job fetches the pinned upstream dependency cache directly; it does not archive the toolchain and Mathlib tree again, which can exhaust the runner's disk during cache saving. Project Lean artifacts are rebuilt in a new directory.

The workflow uploads reports and logs as CI artifacts. A green run means the named checks passed on that commit. It does not certify the 11/5 manuscript's global arithmetic inputs or complete the main Lean proof.

## Theorem application inventory

```sh
python docs/theorem-application-audit/validate.py
```

This structural check runs in CI. Primary-source verification additionally requires the separately restored research workspace; see the [audit instructions](theorem-application-audit/README.md). The current receipt binds the 148-page PDF to the audited TeX. Earlier build receipts are historical.
