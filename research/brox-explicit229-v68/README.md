# Explicit 229-variable quartic: proposed upstream research contribution

This **candidate** is a locally reproducible mathematical/evidence package for the `elliotglazer/diophantine-z-q` review process; it is not a claim of official upstream release or Protocol B acceptance.

For the second review's remaining verification scope see [DEPENDENCY_INDEX.md](DEPENDENCY_INDEX.md) and [check_source_bridge.py](check_source_bridge.py). Read [REVIEW_RESPONSE.md](REVIEW_RESPONSE.md) for the current response to Fable's F1–F3 and Astra's incomplete-review scope. Read [REVIEW_NOTE.md](REVIEW_NOTE.md) for the statement, a proof of the input-preserving rational coordinate equivalence, source dependencies, verified scope, limitations and attribution. The complete arithmetic text is [paper.tex](paper.tex); [source_paper.tex](source_paper.tex) is the previous 229-variable arithmetic argument for comparison.

The final literal polynomial is [quartic229-N15.txt](quartic229-N15.txt): 229 total variables including input, degree 4, 3,312 monomials, maximum coefficient `149^30`, canonical text **74,007 bytes**, SHA-256 `45bdea1ea7876bf6ec10b5427f9403cf1f94c144fab35817aa545bcb2cea1975`.

## Data and exact checks

- `source/quadratic229-v62.json`: authenticated 207-row source with parameter `C=149^N` (pin and hash in `transformation.json`).
- `source/quadratic195.json`: the byte-identical 175-row parent table from Elliot's Version 19 research archive.
- `source/transformation195.json`: pinned source coordinate-change table for the 195-coordinate construction.
- `graft.json` and `contact-change.json`: all 34 coordinate copies, 31 row copies, all contact changes and aggregate identities.
- `check_source_bridge.py`: new standard-library verification of the nine isolated contact helper coordinates, all three complete secant field pairs, x193's imaginary inverse-Vieta product, both inverse-Vieta r components and source hashes.
- `DEPENDENCY_INDEX.md`: pinned Version 20 theorem labels and line ranges for source/consumer review, including the simultaneous prime theorem and prepared pole realization.
- `check_graft.py`: separate standard-library verifier for all retained/copied rows, physical contacts, source point recovery, scalar guards and source coefficient profiles.
- `suppliers/effective_torsion_sums_20261117_v62.tex`: full proof of the effective height inequality with torsion and zero indices, including the sharp 40/2285 numerical corollary.
- `check_arithmetic.py` and `arithmetic_certificate.json`: exact rational inequalities and finite-prime checks for the N=15 proof.
- `transformation.json`: all 229 coordinate scalings and 207 row normalizations.
- `quadratic.json`: all transformed integer quadrics.
- `polynomial.json`: all 3,312 expanded integer-coefficient monomials.
- `quartic229-N15.txt`: complete canonical ASCII expression.
- `build.py`: deterministic reproduction of the three final algebra artifacts.
- `check.py`: standalone exact rational/integer checker; does not import the builder.
- `check_independent.py`: independent SymPy reconstruction, strict parsing, inverse substitution, comparison of arithmetic text and printed exponent tables; only local path resolution was adapted from José Brox's original checker for this folder.
- `upstream/measure_plain_text.py` and `upstream/explicit-record-README.md`: unchanged pinned upstream copies.

From this directory:

```sh
python -B build.py
python -B check_graft.py
python -B check_source_bridge.py
python -B check_arithmetic.py --output arithmetic_certificate_replay.json
python -B check.py
python -B upstream/measure_plain_text.py polynomial.json --verify-text quartic229-N15.txt
python -B check_independent.py --package . --repo . --manuscript paper.tex --output independent_certificate_replay.json
```

The final command requires SymPy; the preceding commands need only the Python standard library. The original verification receipts `certificate.json` and `official_measurement.json` are supplied for comparison, not as independent proof of the source arithmetic hypotheses.

## Integrating into Elliot's repository

Place this folder under `research/brox-explicit229-v68/` on a feature branch whose base is the current upstream `main`. Open a **focused candidate-note pull request**, not an official version bump. Follow `AGENT-INSTRUCTIONS.md`, `CONTRIBUTING.md`, `.github/pull_request_template.md`, `docs/research-review/README.md`, and `docs/release-policy.md` from upstream `main`. Upstream maintainers—not this note—must incorporate any accepted improvement into a complete current TeX/PDF manuscript and obtain the required independent approvals.

Upstream PR #153 was merged on 17 November 2026 as Version 20, containing a 247-variable quartic. Preserve this release and all frozen versions; any next official record requires a later complete manuscript version. The effective N=15 soundness theorem is **new relative to upstream Version 20**, not a consequence of Version 20's ineffective 195-variable theorem. The included supplier proof and paper appendix justify its new height and small-prime steps, subject to reviewer verification. It continues to rely on the previously retained prime-pattern, modular-height, elliptic-group and prepared-pole theorems, which this package does not re-prove.
