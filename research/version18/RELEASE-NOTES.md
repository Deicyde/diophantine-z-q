# Version 18: the 196-variable quartic

Version 18 incorporates José Brox's 196-variable reduction built on Gabriel Conant's 198-variable construction. It retains the complete parent arithmetic proof and adds the elimination lemma and selected unbalanced table from commit `5c35db3253a70b0875acec4b451cdaac4da3c8fd`. The reduced system has 182 quadratic equations. Their sum of squares has degree four, content one and exactly 2,943 nonzero coordinate monomials. The 196 total variables include the input, leaving 195 existentially quantified rational variables. The reduction preserves the rational input projection for each fixed integer `N >= 1`.

The unbalanced presentation selects one fixed polynomial with

```text
N = BB(2^1000)
A = 149^(2*BB(2^1000)+1)
```

Its coefficients are integer polynomials in the fixed integer `A`. Its largest absolute coefficient is `A^2 = 149^(4*BB(2^1000)+2)`, strictly less than `BB(2^2000)`, under the manuscript's stated machine convention. The parent parameter-selection proof transfers through the elimination. The parameter is not another quantified coordinate. The proof bounds a sufficient defining threshold; it does not compute a Busy Beaver value. The general family still defines the integers for every sufficiently large `N`, with a single threshold independent of the input. The coefficient crossover at `N = 7` is a separate comparison, not a defining threshold.

The Tao-Ziegler adaptation asserted without proof in Versions 16 and 17 is now proved in the manuscript. The inverse-theorem dependency uses Candela-Szegedy together with the increment-group argument. The manuscript cites the printed journal statements and page numbers checked against the supplied final edition. The dated comparison distinguishes that local source inspection and the owner's PR118 overrides from gate-reviewer acceptance. Version 18 also incorporates the current foundation repairs and source-application corrections at their points of use.

The complete 198 parent construction and the 214-variable foundation remain as proof dependencies. The original general polynomial and the 314-variable quartic with every coefficient written in decimal remain separate constructions. The latter has 6,672 monomials and coefficient magnitudes below `2^6496`. The selected 196-variable table uses a fixed noncomputable coefficient specification. Degree four is necessary for a single defining polynomial; 196 is an upper bound on the variable count, not a minimum claim.

The package includes the selected unbalanced coefficient table, the exact José196 source pins, the complete supplied Conant package and its upstream José sources, reproducibility checks, the complete numbered manuscript, its build record, source/application records and cumulative handoff. All original source attributions remain. The upstream table's ineffective-threshold metadata is preserved; the fixed BB specialization is the manuscript's separate result. Historical manuscripts and review records retain their original bytes and scopes.

Finite reconstruction verifies the equations, elimination identities, expansions and coefficient statistics. It does not prove the inherited arithmetic characterization. Component review, assembled-proof review, source/PDF correspondence and final protected release acceptance are recorded separately. The final release review is distinct from these component checks; its exact head and decisions must be recorded before official promotion.

The retained 214-variable exposition now cites the sections proving its inputs instead of calling the construction proposed or making its conclusion conditional on separately named prerequisites. The current dependency inventory locates the geometry, modularity, height, rank, restricted-converse, prime-pattern and pole arguments. This change does not add a hypothesis, alter the selected polynomial, compute an ineffective constant or change the AI usage statement. The new predecessor-transport certificate checks all printed 214 rows and the exact 212/204 transformations; it complements the arithmetic proofs rather than replacing them.
