# Version 7: the 962-variable quartic and theorem inventory

The manuscript retains three polynomials: the original large construction, the fully expanded 4,973-variable Version 4 quartic, and the 962-variable quartic. The last has 961 witnesses in addition to its input, 919 quadratic residuals, degree four, and 55,409 nonzero monomials. Its primitive content is one and its largest coefficient magnitude is exactly `64*3^(2^28)`.

## Polynomial and finite checks

The [coefficient table](../../quartics/quartic-962/polynomial.json) lists every monomial, with coefficients expressed using the fixed integer `S=3^(2^27)`. It has SHA-256 `6b798de7d00ac3c7d725ca0a69d39f1eac1ddb02fee2756cb6323770b952af32`. The [package manifest](../../quartics/quartic-962/MANIFEST.json) pins the source, compiler, proofs and preserved review evidence. Its SHA-256 is `36fca72cb0eb126193ffa43d890ff09d5e29cbf1274561d2632ed1e227163787`.

From the repository root, with Python 3.10+ and Node.js 18+:

```sh
python -E -B scripts/check_quartic962.py --out build/quartic-962-reproduction
```

The output directory must be new and outside the package. The supported command rebuilds seven artifacts, checks every gate and compiler operation, and requires byte identity with the complete table. It also checks the actual emitted coordinate identities and anchors. The mathematical nonzero-domain arguments and arithmetic characterization remain separate source-level proofs.

The package preserves historical metadata, including earlier pending-review strings, original paths in some archived scripts, and a Windows-1252 README. Later pinned reviews record acceptance of the exact final artifacts. Use this UTF-8 guide and the command above as the current entry point; archived workspace scripts are not all portable commands.

## Source-application inventory

The inventory identifies exact theorem versions, application hypotheses, maps, conventions, translations, source qualifications, and independent review evidence. It preserves the older application ledgers and binds changed or new text to its own reviewed fragment. Frei–Tinková is methodological provenance in Version 7, not an assumed theorem. The Gaussian replacement uses Mitsui, Green–Tao and the listed ordinary-prime transference inputs.

```sh
python -E -B docs/quartic-962/inventory.py validate --repo . --manuscript manuscripts/quartic_v7.tex --expected-input-sha256 36646fd26f5adcaed33315605e4b1c333c1e60f5c917aeeda63976614823a0f5
python -E -B docs/quartic-962/test_inventory.py
```

The degree-four obstruction is proved in the manuscript from the agentic notes. Its application of Kollár uses the explicitly identified author version of a published theorem; the journal metadata was verified, but the final typeset statement was not compared. The Dodos–Kanellopoulos and inherited source-version qualifications are retained as well.

The register covers 125 external application families, eight inherited source ledgers, 151 result environments, 226 citations and 519 references. Start with [coverage.json](coverage.json), then [theorem-applications.json](theorem-applications.json), [internal-results.json](internal-results.json) and [dependency-graph.json](dependency-graph.json). The authored [new-applications.json](new-applications.json) supplies the source and convention records. Twenty-five adversarial tests check document binding. The [independent review](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/docs/quartic-962-validation/inventory-review.json) records its mathematical coverage and provenance checks. Historical records retain their original reviewer wording; they are not evidence of independent human peer review.

`PASS_DOCUMENT_BINDING` certifies the documented identity and coverage checks. It is not a machine proof of the mathematics or a claim of independent human peer review. See [building instructions](../building.md), [research history](../../research/version6/README.md), and the [handoff guide](../../handoff/README.md).

The [6 November Gaussian audit](gaussian-audit-20261106.md) records four further independent component reviews, the integrated repairs, and their limits.
