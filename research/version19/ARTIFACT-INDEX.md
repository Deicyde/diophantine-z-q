# Version 19 artifacts

| Purpose | File |
| --- | --- |
| Complete manuscript | [PDF](../../manuscripts/quartic_v19.pdf), [TeX](../../manuscripts/quartic_v19.tex) |
| Source/PDF provenance | [Build record](BUILD.json), [release manifest](RELEASE-MANIFEST.json) |
| New arguments and their consumers | [Dependency map](DEPENDENCIES.md), [release notes](RELEASE-NOTES.md) |
| Earlier local component reviews and limits | [Original reports](reviews/README.md) |
| Selected original construction data | [Input inventory](construction/INPUTS.json), [attribution](construction/NOTICE.md) |
| Independent finite checks | [Runner](construction/check.py), [instructions](README.md#reproduction) |
| Explicit 250-variable polynomial | [Plain algebraic expression](construction/plain-text/quartic250-decimal.txt), [format](construction/plain-text/FORMAT.md), [JSON](construction/coefficients/quartic250-decimal.json) |
| Cumulative release package | [Packing and reconstruction](CUMULATIVE-HANDOFF.md) |

The 195-variable parameter is fixed by the Busy Beaver convention in the
manuscript. The checkers manipulate its coefficient polynomials symbolically;
they do not calculate that parameter. The 250-variable expression has all its
coefficients written in decimal. Finite identities and source/PDF hashes do not
replace review of the arithmetic proof.
