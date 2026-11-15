# Version 18

The complete [PDF](manuscripts/quartic_v18.pdf) and [TeX](manuscripts/quartic_v18.tex) contain Jose Brox's 196-variable quartic, its reduction from Gabriel Conant's 198-variable construction, and the full inherited arithmetic argument. The quartic has 182 quadratic summands and 2,943 nonzero monomials. Counts include the input, so 195 variables are existentially quantified.

The coefficients are integer polynomials in the fixed integer `A=149^(2*BB(2^1000)+1)`. Their maximum absolute value is `A^2`, strictly less than `BB(2^2000)`, with the manuscript's two-symbol, blank-tape, running-time convention. Neither `A` nor `N=BB(2^1000)` is an additional coordinate. This is a coefficient specification, not a decimal expansion or an algorithm for evaluating BB.

The original large polynomial and the 314-variable decimal quartic remain separate results. Degree four is minimal for a single defining polynomial; no minimal-variable-count claim is made. Version 17 and all earlier released manuscript files are preserved unchanged.

- [Release guide and scope](research/version18/README.md)
- [Changes and corrections](research/version18/RELEASE-NOTES.md)
- [Artifacts and sources](research/version18/ARTIFACT-INDEX.md)
- [Reproduction](research/version18/REPRODUCTION.md)
- [Build record](research/version18/BUILD.json)
- [Cumulative handoff](research/version18/CUMULATIVE-HANDOFF.md)

The final protected review must cover the assembled argument, incorporation of its component results and the actual source/PDF pair. Finite reconstruction and successful compilation establish their stated checks only. The historical [Version 17 guide](CURRENT_VERSION17.md) retains its own scope.
