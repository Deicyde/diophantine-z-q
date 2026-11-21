# The 11/5 manuscript

*ℤ is Diophantine in ℚ*, November 5, 2026 revision, `diophantine_zq.tex` in this
repository (SHA-256 `cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`).
Locators are the TeX labels, which are stable across builds.

## Theorem 1.1

`thm:target`, Section 1: the polynomial definition of the integers. Lemma 1.2
(`lem:assembly`) assembles it from the inputs G, M, H, PC, C and B.

## Proposition 3.1

`prop:generator`, Section 3: $P_0$ has infinite order and $2E(K_0)=\mathbb ZP_0$. The proof
cites the Mordell–Weil theorem after the two-isogeny descent and the torsion bound.

## Theorem 4.1

`thm:height`, Section 4: the six-contact estimate.

## Theorem 5.2

`hyp:PC`, Section 5: pole completeness. Theorem 5.3 (`hyp:RC`) is the restricted converse
from which Section 5.1 derives it.

## Theorem 5.3

`hyp:RC`, Section 5: the restricted converse. For every positive squarefree $\ell\equiv11\pmod{12}$,
$\mathbb Z_2$-corank $1$ of $\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)$ implies
$\operatorname{ord}_{s=1}L(E_\ell,s)=1$, where $E_\ell:y^2=x(x-\ell)(x+3\ell)$.

## Section 5.1

The subsection "The exact descent reduction" of Section 5 (`sec:pole`): the simultaneous 2-descent that
derives Theorem 5.2 from Theorem 5.3, Lemma 5.4 and Lemma 5.5.

## Lemma 5.4

`lem:corank`, Section 5.1: for an elliptic curve with full rational two-torsion, a 2-Selmer group of
dimension three gives $2^\infty$-Selmer corank one.

## Lemma 5.5

`lem:forward-rank`, Section 5.1: analytic rank $r\le1$ gives rank $r$ and a finite Tate–Shafarevich group.

## Section 7

`sec:rc`: the restricted converse and its dependency order.

## Section 8

`sec:arithmetic`: actual classes, local conditions and central comparison.

## Section 9

`sec:limits`: the two limits and determinant transfer.

## Appendix E

`app:even-source`: fixed-form arithmetic and the even coefficient source.

## Appendix F

`app:odd-source`: actual odd theta forms and their operators.

## Appendix G

`app:endpoints`: nonvanishing, normalization and the final family.

## Proposition 6.2

`prop:fixed-prime-pattern`, Section 6: the fixed twenty-two-prime pattern.

## Proposition 12.1

`prop:cutoff`, Section 12: the literal cutoff, including the catalogue bound
$H_{\max}<2^{W^3}$ obtained from the explicit progression estimate.
