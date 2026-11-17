---
article_id: af_9795dfc6482d108fba24362b
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves40.javanpeykarPrintedMapHF
---

# Javanpeykar's bound for curves with a Belyi map

The *Javanpeykar statement* is the following assertion. Let $X_0$ be a smooth proper geometrically
connected curve over a number field $K$ and $X$ its base change to an algebraic closure
$\overline K$, a projective curve of genus $g\ge1$. Let $W$ be an abelian variety over $\overline K$
that represents the degree-zero part of the Picard functor of $X$, $V$ an abelian variety over $K$
whose base change to $\overline K$ is $W$, and $\beta:X\to\mathbf P^1_{\overline K}$ a Belyi map (a
finite morphism unramified outside $0,1,\infty$) of degree $d$. Then every stable Faltings height
$h$ of $V$, built as for [Bost's lower bound](bost-lower-bound.md), satisfies
$$h\le13\cdot10^6\,g\,d^5.$$

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Javanpeykar's Theorem 1.1.1 bounds the Faltings height of
the curve by its Belyi degree, and his paper identifies that height with the stable Faltings height
of the Jacobian. The statement takes the degree of a given Belyi map in place of the least one, and a
model $V$ of the Jacobian over $K$. The project's earlier form, for a curve with a rational point
and a Belyi function over $K$, is proved here from this one. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Javanpeykar bound](../../../sources/height-decomposition-locators.md#javanpeykar-bound)
