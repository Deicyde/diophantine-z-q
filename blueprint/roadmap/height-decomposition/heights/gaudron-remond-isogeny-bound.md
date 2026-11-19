---
article_id: af_7e432b9262db4dfd0cf66150
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves71.gaudronRemondThm14AnSS
---

# The isogeny theorem of Gaudron and Rémond

The *isogeny statement* is the following assertion. Let $A$ and $B$ be abelian varieties over a
number field $K$ of degree $d$ that are isogenous over $K$, with $\dim A=g$, and let $h_F(A)$ be a
stable Faltings height of $A$, built as for the [lower bound](bost-lower-bound.md). Then there are
isogenies $A\to B$ and $B\to A$ over $K$ of degree at most
$$\kappa=\Bigl((14g)^{64g^2}\,d\,\max\bigl(h_F(A),\log d,1\bigr)^2\Bigr)^{1024g^3}.$$

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. It is Theorem 1.4 of Gaudron and Rémond for isogenies over the
base field, with the stable height in Faltings' original normalization and semistable reduction in
its printed form: the identity component of the special fibre is semi-abelian over the residue field
and over its algebraic closure. A further reading of semistability, as the absence of $\mathbb G_a$
(SGA 7 IX 2.1.5), is still to be matched. It is a hypothesis, not proved here.

## Depends on

- [The lower bound for the Faltings height](bost-lower-bound.md)

## Sources

- [Gaudron-Remond isogeny bound](../../../sources/height-decomposition-locators.md#gaudron-remond-isogeny-bound)
