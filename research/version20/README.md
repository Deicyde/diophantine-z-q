# Version 20

The [manuscript](../../manuscripts/quartic_v20.pdf) and
[TeX source](../../manuscripts/quartic_v20.tex) give Gemini 4 Carbon's explicit
247-variable quartic, built on José Brox's construction. It has 3,385 nonzero
monomials and largest absolute coefficient

```text
149^10220 + 298442980098761875927809873 < 2^73780.
```

The [plain algebraic expression](construction/inputs/carbon/tables/explicit247/quartic247-decimal.txt)
is exactly 96,712 bytes in the [repository notation](../../docs/explicit-record/README.md).
Its SHA-256 is `455afb0b7143654119db3a68a85fec2fde566cf7fbdf3f7c84bd5d75b32719b9`.
The [JSON coefficient table](construction/inputs/carbon/tables/explicit247/quartic247-decimal.json)
is another representation of the same polynomial.

The 195-variable polynomial with Busy Beaver coefficients is unchanged. The
250-variable explicit polynomial remains in the manuscript as an intermediate
construction with smaller coefficients. Counts include the rational input.
All released Version 19 and earlier files remain unchanged.

## Reproduction

From the repository root, using Python 3.12 or later:

```sh
python -B research/version20/construction/check.py
python -B scripts/check_current_manuscript.py
python -B scripts/build_paper.py
```

The finite checks authenticate all selected new inputs, run the retained Version
19 checks, strengthen the 250-coordinate checks, verify every 247-coordinate
transformation, and parse the actual printed 195, 250 and 247 tables. They also
compare the printed scaling and permutation tables with the certificates.
Results are written under `build/version20/` and `build/version19/`.

The [build record](BUILD.json) binds the committed PDF to its source and engine.
The existing paper CI rebuilds the current manuscript; its Tectonic output need
not be byte-identical to the committed MiKTeX PDF. This PR changes no workflow:
the existing construction CI still runs the Version 19 checks. The Version 20
check command above is run separately and its result is supplied for review.
Finite calculations do not establish the arithmetic characterization or supply
independent acceptance of the assembled manuscript.

See the [dependency map](DEPENDENCIES.md), [corrections ledger](CORRECTIONS.md),
and [release notes](RELEASE-NOTES.md).
