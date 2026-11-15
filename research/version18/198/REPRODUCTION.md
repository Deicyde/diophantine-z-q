# Reproduce the 198 construction and printed rows

This directory contains portable copies of the independent finite construction checker, row generator and literal TeX roundtrip checker. The selected polynomial is the unbalanced 198-variable construction. The supplied balanced table is checked as historical comparison; it is not the polynomial-in-A presentation selected for Version 18.

The scripts use explicit input and output paths. They import no supplied package producer or checker. They need no network or credentials. The source package is read only. Do not use Python -O or -OO; the scripts reject those modes because they require assertions.

## Environment

Use Python 3.10 or later. The construction checker requires SymPy 1.14.0, specified in requirements.txt; the row generator and roundtrip checker use only the Python standard library. This portable replay was tested with Python 3.14.7 and SymPy 1.14.0. No package was installed by the preparation task.

## Inputs

INPUT-FILES.json enumerates exact paths, byte lengths and SHA-256 hashes.

- upstream/H10-quartic198.zip is the unchanged supplied archive, SHA-256 33439f62ec243375b19f50c2801cad36500f21902285a82e5c08984a0c5568c4.
- upstream/H10-quartic198/ contains all 90 authenticated package files in their original layout.
- provenance/PACKAGE-PINS.json is the unchanged historical package inventory. Its old zip field records a host path; the portable checker never opens that field. It authenticates the explicit --archive argument against zip_sha256.
- tex/q198-rows.tex is the frozen standalone row component, SHA-256 a592e13b8d92fbd1602796a81b93cb035728dbde8d96c1de72dbf8c4e97e7cfc.
- checks/portable_io.py is required beside each checker.

The construction check authenticates all 90 extracted files, not just the numerical tables. Its algebra reads the 204 unbalanced source, the affine-200 quadratic and quartic tables, the inverse-Vieta rescaling weights, the 198 unbalanced and balanced quadratic/quartic tables, and the balancing weights. The exact paths are listed in INPUT-FILES.json. Retaining the full supplied package is the simplest way to meet this input contract.

## Commands

From the repository root, run each command on one line. Output goes under build/version18-198, outside the source package.

    python -B research/version18/198/checks/independent198.py --package research/version18/198/upstream/H10-quartic198 --pins research/version18/198/provenance/PACKAGE-PINS.json --archive research/version18/198/upstream/H10-quartic198.zip --output build/version18-198/independent198-result.json

    python -B research/version18/198/checks/generate_q198_tex.py --package research/version18/198/upstream/H10-quartic198 --output-dir build/version18-198/generated

    python -B research/version18/198/checks/verify_q198_tex.py --package research/version18/198/upstream/H10-quartic198 --rows build/version18-198/generated/q198-rows.tex --output build/version18-198/generated-ROUNDTRIP.json

To check the distributed standalone rows directly:

    python -B research/version18/198/checks/verify_q198_tex.py --package research/version18/198/upstream/H10-quartic198 --rows research/version18/198/tex/q198-rows.tex --output build/version18-198/distributed-ROUNDTRIP.json

Absolute paths work from any working directory. Quote paths containing spaces. The original public layout is a convention, not a hardcoded script dependency.

The generator also writes preview.tex beside the generated component. Compiling that wrapper is optional visual inspection, not part of the coefficient roundtrip. The checker expects the standalone row component, not an entire assembled manuscript with other equation environments. The final manuscript must separately bind the incorporated component and its PDF rendering.

## Checked results and limits

The portable construction replay completed 50,684 assertions and authenticated 90 package files. It reconstructs the 204-to-affine-200-to-inverse-198 transformations and independently expands the quadratic residuals. The unbalanced result has 198 coordinates including the input, 197 existential variables, 184 quadratic rows, degree four, content one, and 2,945 nonzero coordinate monomials. It checks the exact coefficient expression

    P_A = P_0 - 2 A x104 - 44402 A x104^2 x116 + A^2 x104^2.

Its family parameter is A=149^(2N+1). The coefficient maximum is max(H0,A^2); the crossover N=53 is only a coefficient comparison. These finite checks do not prove a defining threshold or evaluate Busy Beaver.

The row replay parses all 77 explicit integer aliases, 198 coordinate records and 184 displayed equations. It reconstructs the coefficients and expands their sum of squares to match all 2,945 terms. Generated rows were byte-identical to the frozen component. The coordinate convention is Y_0=input x, with delivered source coordinate i corresponding to Y_(i-1).

The validation used a relocated directory with spaces and an unrelated working directory. It rejected a damaged archive, an altered printed integer coefficient, optimized Python and an output path inside the input package. All source-layout files remained byte-identical. Its child environment contained only the documented runtime keys, with no credentials.

provenance/CHECKER-ADAPTATION.json and provenance/diffs/ show the exact path and UTF-8 changes. The mathematical expression/comparison bodies are unchanged from the original source snapshots. evidence/ records the finite replay, not independent acceptance of the arithmetic proof, Busy Beaver proof, final manuscript, source/PDF pair or release gate.
