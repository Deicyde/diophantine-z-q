# Version 19

The complete [PDF](manuscripts/quartic_v19.pdf) and [TeX](manuscripts/quartic_v19.tex)
incorporate José Brox's 195-variable family and Gemini Carbon's explicit
250-variable quartic built from Brox's construction. Counts include the input.

The 195-variable polynomial has 2,956 nonzero coordinate monomials. Its
coefficients are integer polynomials in the fixed integer
`C = 149^BB(2^1000)`, with absolute values below `BB(2^2000)` under the
manuscript's two-symbol, blank-tape running-time convention.

The explicit polynomial has 3,362 nonzero monomials and coefficients below
`2^6483`. Its [plain algebraic expression](research/version19/construction/plain-text/quartic250-decimal.txt)
is 85,737 bytes, using the [documented format](research/version19/construction/plain-text/FORMAT.md).
The manuscript supplies both rational-solution directions and the printed
quadratic tables. The original large construction and the earlier quartics are
retained; every earlier released manuscript remains unchanged.

- [Release guide](research/version19/README.md)
- [Artifact index](research/version19/ARTIFACT-INDEX.md)
- [New arguments and dependencies](research/version19/DEPENDENCIES.md)
- [Build record](research/version19/BUILD.json)
- [Cumulative handoff](research/version19/CUMULATIVE-HANDOFF.md)

Final acceptance is the protected review of the actual release PR and is
recorded in its release assets. Finite checks alone do not establish the
arithmetic theorem or assembled-proof acceptance.
