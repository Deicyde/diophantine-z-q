# Author serialization notes

This is an additive manuscript serialization. It changes no frozen polynomial,
proof, application contract, source theorem, reviewer record, or acceptance.
The 214 packet source commit is `110cf72565be326fd567cd1a64a3b2e00213dcd1`.
The current upstream foundation is the Version 16 target selected by
`docs/current-manuscript.json`, SHA-256
`aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74`.
The explicit source/consumer transition is
`../quartic214-manuscript-review/FOUNDATION_TRANSITION.md`.

`assemble.py` uses the Python standard library and makes no network requests,
symbolic expansions, TeX builds, or acceptance records. Its `--check` mode
reconstructs both generated files in memory and compares their exact bytes.
`quartic214.tex` is the complete, standalone TeX source. `SOURCE_SPANS.json`
binds input byte hashes and source-line or JSON-pointer spans to its TeX lines.

Part I contains the new theorem, notation, all 214 coordinate names, all 188
primitive integral quadratic rows, every line of the public assembly and
proof files, every selected Markdown/TeX source fragment, the raw224 proof,
finite-certificate links and hashes, and the complete primary-source metadata.
The polynomial is specified exactly as the unweighted sum of these 188 row
squares. Long row coefficients are printed as exact base-ten block sums;
the assembler does not expand the 2919-monomial quartic.

Part II retains the entire current Version 16 mathematical body with its
bibliography and historical provenance. Its original `maketitle` and duplicate
table of contents are publication wrappers replaced by the unified front
matter. Its original abstract is retained. Its section and equation counters
are restored; separate hyperlink namespaces prevent collisions with Part I.
Only line endings are normalized in the retained mathematical body. Four
separate invisible navigation labels locate corrected applications; the exact
mapped source blocks concatenate to the complete original mathematical body.
Generated PDF destinations are unique without changing printed numbers. The
original byte hash remains separately bound. The frozen Version 15 source is
also byte-bound as historical provenance for the earlier author packets.

ASCII mathematics in the Markdown sources is typeset into mathematical TeX.
Balanced spans retain quantified conditions containing spaces. Script operands
retain their full grouping, including negative indexed exponents. Source set
braces are visible delimiters, while script braces remain grouping. Root
operands are explicit. Bare ASCII `Q`, `Z` and stars retain their source
notation rather than receiving a global semantic interpretation.

Several notation resolutions are source-specific and recorded in the map:
the summation Sigma in the different, metric and aggregate source files;
the aggregate function `F+` in its two proof occurrences; the metric source's
direct-image star and conjugate differentials; the evaluation/different
target projective line; degree-zero differential cohomology `H0(...)`; and the
uniform proof's `mathfrak_b` pole-input notation. Control sequences and their
space-separated arguments remain in the same mathematical span.
Selected TeX fragments have local labels/references namespaced and their
bibliography keys matched to the complete retained bibliography. Their
historical `Logs` citation resolves to the actual retained V15 logarithm
section. No substitute arithmetic theorem is introduced.

The operative averaging route is visibly the published product construction.
The old H3 quotient route and coarse conductor fragments are retained with
explicit supersession notices. Their historical scope statements are not
silently promoted to acceptance of this serialization. The theorem keeps its
fixed ineffective uniform threshold, and `N >= 53` remains coefficient-only.

The author lane ran no TeX build. The root lane owns bounded serial PDF
compilation, rendered inspection, release hashes and publication. Source-map
coverage, deterministic reconstruction, compilation and finite algebra checks
are bounded checks; they do not establish the arithmetic theorem or official
Protocol D acceptance. Required independent review is authored separately.
