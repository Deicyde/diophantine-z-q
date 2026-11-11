---
article_id: af_29d9111307cfc70e0506eaaa
---

# The other templates

Besides membership and raw addition, the core elliptic templates express the local
parameter $z=-x/y$, the inverse abscissa and the truncated formal logarithm, whose seven
coefficients are $16575(-1)^j\binom{2j}{j}/(4j+1)$.

- [The local parameter template](template-raw-z.md)
- [The inverse abscissa template](template-raw-inverse-x.md)
- [The truncated logarithm template](template-log25.md)
- [The coefficients of the truncated logarithm](log25-coefficients.md)

The multiplication certificate is assembled from the pole polynomial, twelve local tests,
the normalized slope certificate and the height certificate. The pole template's relation is
the pole predicate $\Phi$ of pole completeness.

- [The pole template](template-pole.md)
- [Semantics of the pole template](pole-semantics.md)
- [The test-group template](template-test-group.md)
- [The slope template](template-slope.md)
- [The height certificate template](template-height-certificate.md)

Fixed scalar multiples are expressed with division polynomials, and the guard excludes
exactly the false triples of codes in the finite box.

- [The fixed-scalar templates](template-fixed-scalar.md)
- [The guard template](template-guard.md)
- [Semantics of the guard template](guard-semantics.md)

The multiplication template conjoins four scalar shifts, the height certificate and the
guard. The natural template expresses a code of a natural number as a sum of four squares;
given the multiplication statement, its relation holds exactly on the codes of natural numbers.

- [The multiplication template](template-multiply.md)
- [The natural-code template](template-natural.md)

Its semantics, the natural-code predicate, is proved in the translation chapter:
[the natural-code predicate](../../compiler/translation/natural-code-semantics.md).

The value templates encode signed indices, absolute values, the coordinate window, the six
raw tests with the pole predicate, and the six exceptional values.

- [The signed-encoding template](template-signed-encode.md)
- [The absolute-value template](template-abs.md)
- [The coordinate-window template](template-close-coordinates.md)
- [The value-test template](template-value-test.md)
- [The exceptional-values template](template-exceptions.md)

The library lists the 23 templates in order, including five fixed-scalar templates for the
constants of the natural precision polynomial.

- [The template library](template-library.md)
