---
article_id: af_9795dfc6482d108fba24362b
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves71.javanpeykarThm111An
---

# Javanpeykar's bound for curves with a Belyi map

The *Javanpeykar statement* is the following assertion. Let $\overline{\mathbb Q}$ be an algebraic
closure of $\mathbb Q$ and $X$ an integral, projective, smooth proper geometrically connected curve
over $\overline{\mathbb Q}$ of genus $g=\dim H^1(X,\mathcal O_X)\ge1$ that has a Belyi map, a finite
morphism $X\to\mathbf P^1_{\overline{\mathbb Q}}$ unramified over
$\mathbf P^1\setminus\{0,1,\infty\}$; let $\deg_B(X)$ be the least degree of a Belyi map of $X$. Let
$W$ be an abelian variety over $\overline{\mathbb Q}$ that represents the degree-zero part of the
Picard functor of $X$, with the group law given by the tensor product of line bundles. Then every
stable Faltings height $h$ of $W$ satisfies $h\le13\cdot10^6\,g\,\deg_B(X)^5$; here a stable
Faltings height of $W$ is a stable Faltings height, built as for the
[lower bound](bost-lower-bound.md), of an abelian variety $V$ over a number field
$L\subset\overline{\mathbb Q}$ whose base change to $\overline{\mathbb Q}$ is isomorphic to $W$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Javanpeykar's Theorem 1.1.1 bounds the Faltings height
of the curve by its Belyi degree, and §2.3 of his paper identifies that height with the stable
Faltings height of the Jacobian; the statement is the composite of the two, stated for the Jacobian.
Semistability is that of the Néron model of the Jacobian, not the semistability of a model of the
curve that the paper uses. Reaching it from the print also takes the fact that the height of a Néron
model with semistable reduction everywhere does not depend on the number field or on the model
(Faltings 1983; Deligne, Sém. Bourbaki 616), so that every stable height of $W$ in this sense is the
stable Faltings height of the Jacobian. It is a hypothesis, not proved here.

## Depends on

- [The lower bound for the Faltings height](bost-lower-bound.md)

## Sources

- [Javanpeykar bound](../../../sources/height-decomposition-locators.md#javanpeykar-bound)
