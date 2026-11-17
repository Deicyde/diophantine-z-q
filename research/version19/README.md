# Version 19

The complete [manuscript](../../manuscripts/quartic_v19.pdf) and
[TeX source](../../manuscripts/quartic_v19.tex) incorporate José Brox's
195-variable quartic family and Gemini Carbon's explicit 250-variable quartic,
which uses Brox's construction as its arithmetic foundation. Both counts include
the rational input. Earlier published manuscripts remain unchanged.

The 195-variable system has 175 quadratic residuals and 2,956 coordinate
monomials after summing their squares. Its coefficients are integer polynomials
in the fixed integer `C = 149^BB(2^1000)`, with the manuscript's two-symbol,
blank-tape running-time convention. Every coefficient has absolute value less
than `BB(2^2000)`. The finite checks do not evaluate Busy Beaver.

The explicit polynomial uses `N = 10220`, 250 coordinates and 222 quadratic
residuals. It has 3,362 nonzero monomials. Its largest absolute coefficient is

```text
149^898 + 1747145497790223592810060471184416344603224790540808983 < 2^6483.
```

The [plain algebraic expression](construction/plain-text/quartic250-decimal.txt)
is exactly 85,737 bytes. The [format definition](construction/plain-text/FORMAT.md)
specifies every character, including the absence of a final newline. The
[decimal coefficient table](construction/coefficients/quartic250-decimal.json)
contains the same polynomial in JSON.

## Reproduction

From the repository root, with Python 3.12 or later:

```sh
python -B research/version19/construction/check.py
python -B scripts/check_current_manuscript.py
python -B scripts/build_paper.py
```

The first command checks selected source hashes, the printed 195-coordinate
transformation, the explicit 250-coordinate transformation and expansion, the
retained printed parent equations, and the plain-text round trip. Results are
written under `build/version19/`. It executes only the included independent
checkers, never the upstream producers. These are finite algebra checks, not
proofs of the arithmetic characterization or independent release acceptance.

The matching committed PDF has its engine, inputs and source hash recorded in
[BUILD.json](BUILD.json). CI also rebuilds the paper with its pinned Tectonic
engine; that PDF need not have identical bytes. See the
[release notes](RELEASE-NOTES.md) and [dependency map](DEPENDENCIES.md) for the
mathematical scope and the relation to Version 18.
