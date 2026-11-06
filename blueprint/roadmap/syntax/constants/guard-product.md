---
article_id: af_583092dc0956b4a2983cff03
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.guardPoly, ZInQ.Syntax.guardPoly_eval_eq_zero_iff
---

# The finite false-triple product

For an integer $T\ge0$, a triple $(a,b,c)\in\mathbb Z^3$ is a false triple in the box if
$|a|,|b|,|c|\le T$ and $ab\ne c$. For such a triple write the fifteen coordinates of
$(\iota(a),\iota(b),\iota(c))$, in point-major order, as reduced fractions $A_j/B_j$ with
$B_j>0$ ($j=1,\dots,15$), and put $D_{abc}=\prod_{j=1}^{15}B_j$. The guard polynomial is
$$G_T(X_1,\dots,X_{15})=\prod_{\substack{(a,b,c)\in[-T,T]^3\\ ab\ne c}}\ \sum_{j=1}^{15}\Bigl(D_{abc}X_j-\frac{D_{abc}}{B_j}A_j\Bigr)^2\ \in\mathbb Z[X_1,\dots,X_{15}],$$
the product over the finite set of false triples (empty product $1$). Each factor has
integer coefficients because $B_j\mid D_{abc}$. The constructor
$\mathrm{guard}\ e\ (a_1,\dots,a_{15})$ denotes $G_{\mathrm{val}(e)}$ at the polynomials of its
argument nodes; the specification uses only $e=T$.

The polynomial is never expanded: its arithmetic zero set is described by the guard
semantics, and its size by the size chapter.

The specification describes the coordinates of $\iota(n)$, $n>0$, through division
polynomials at $P_0$, namely $x_n=x(P_0)-\psi_{n+1}(P_0)\psi_{n-1}(P_0)/\psi_n(P_0)^2$ and
$y_n=\psi_{2n}(P_0)/(2\psi_n(P_0)^4)$, with $\iota(-n)$ obtained by negating the ordinate. These
are the coordinates of $[n]P_0$ by the multiplication-by-$n$ formulas, because $P_0$ has
infinite order; the definition here uses $\iota$ directly.

This is a definition.

## Depends on

- [The codes of multiples of the generator](../../model/point-codes.md)

## Informally uses

- [The multiplication-by-n formulas](../division-polynomial-multiplication.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
