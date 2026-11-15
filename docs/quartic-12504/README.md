This inventory covers the exact 12,504-variable quartic in
[`quartic_12504.tex`](../../quartic_12504.tex) and
[`quartics/quartic-12504/`](../../quartics/quartic-12504/).
The source uses reciprocal logarithms with precision 64 for the common
denominator and Lucas numerators, precision 16 for beta, 41 contacts,
24 anchor squarings, and scalar order 48. The accepted height exponent is 24.

[`theorem-applications.json`](theorem-applications.json) states the current
source theorem, its new local lemmas, the algebraic transformations, and
the exact artifact pins. [`dependency-closure.json`](dependency-closure.json)
connects that theorem to eleven inherited arithmetic families and their
source-application ledgers. The new reciprocal source requires its own
arithmetic proof; the original source theorem alone does not justify it.

[`baseline-bridge.json`](baseline-bridge.json) maps every historical
application excerpt to identical current text. The earlier 82 application
decisions remain tied to the frozen
[`audited-baseline.tex`](../theorem-application-audit/source/audited-baseline.tex).
This bridge does not assign those reviews to new text. Later H5 material
is covered by the retained [H5 ledgers](https://github.com/elliotglazer/diophantine-z-q/tree/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/docs/degree8-original/research/accepted-h5)
and current manuscript proof. The reciprocal additions have their own
[review records](https://github.com/elliotglazer/diophantine-z-q/tree/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/docs/quartic-12504/reviews).

The inherited source-version qualifications remain in force. In particular,
the Yuan application uses the recorded author-attested English translation;
the Pan application records the published Calegari formulation and specified
Pan author proof; and the prime-pattern ledger retains its stated corrected
author-version and erratum conventions. Imported historical ledgers may
describe an earlier padded constant; the current H5 proof and acceptance
record govern the current constant. These records are mathematical evidence,
not a claim of a complete Lean verification.

[`evidence-import-manifest.json`](evidence-import-manifest.json) identifies
the copied plaintext evidence. Publisher PDFs, downloaded scans, and HTML
are not redistributed here. Their recorded URLs, versions, locators, and
hashes identify the consulted primary sources. A historical PDF locator is
provenance, not an assertion that the PDF is included in this repository.

Run from the repository root:

```sh
python docs/theorem-application-audit/validate.py
python docs/quartic-12504/validate.py
```

The current validator writes `build/quartic-inventory.json`. It checks byte
bindings, exact excerpt transport, labels, and dependency reachability.
It does not prove the arithmetic statements or repeat certificate replay.
Use the separate [reproduction runner](../../quartics/quartic-12504/reproducibility/README.md)
for the source audit, malformed-input tests, full certificate replay,
complete coefficient expansion, and fresh construction.
