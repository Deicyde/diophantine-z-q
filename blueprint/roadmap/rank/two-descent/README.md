---
article_id: af_a7b01fdbb71a05f3f27da3ad
---

# The complete 2-descent on a congruent number curve

For a field $K$ with $2\ne0$ and $d\in K^\times$, the curve $C_d:y^2=x(x-d)(x+d)$ has full
rational two-torsion. Its complete 2-descent map $\delta_d$ sends a point to the pair of Kummer
classes at the roots $0$ and $d$: $(x,y)\mapsto(x,x-d)$ in $(K^\times/K^{\times2})^2$, with the
usual values at the torsion points (Silverman, Proposition X.1.4). At the root $0$ the formulas are
those of the Kummer map $\alpha_b$ of the [two-isogeny descent](../../model/descent/kummer-map.md).
The Kummer map $\kappa_{b,e}$ at a general root $e$ is a homomorphism by the chord argument.
Over $\mathbb Q$ the descent map has kernel exactly $2C_d(\mathbb Q)$, by an explicit halving
formula. Read in square classes, it agrees with the
[Kummer map of the coverings](../../selmer/kummer-map.md), so over $\mathbb Q$ the pairs $s(P)$ of
squarefree representatives $r(c)$ of its values lie in $\mathrm{Sel}_2(C_d)$. A count in finitely generated abelian groups then gives RK9: positive rank
and a Selmer group of order $8$ make every Selmer class come from a rational point.

Over a general field $K$, $d$ is a nonzero element of $K$ and $C_d:y^2=x^3-d^2x$ is the curve
$E_{-d^2}$; over $\mathbb Q$, $d$ is a positive integer, and $C_d$ and $\mathrm{Sel}_2(C_d)$ are those
of the [Proposition 0 chapter](../../selmer/README.md). Throughout, $u\equiv v$ means that $u/v$ is a
nonzero square.

## The Kummer map at a root

- [The Kummer map at a root of the cubic](kummer-map-at-root.md)
- [The Kummer map at a root is a homomorphism](kummer-map-at-root-homomorphism.md)

## The descent map of $C_d$

- [The complete 2-descent map of a congruent number curve](descent-map.md)
- [The complete 2-descent map is a homomorphism](descent-map-homomorphism.md)
- [The descent map is the Kummer map of the coverings](descent-map-kummer.md)

## Halving and two-torsion

If $x$, $x-d$ and $x+d$ are squares, then $(x,y)$ is twice a point, by an explicit formula for the
half. The points of order dividing $2$ are $O$ and the three points $(e,0)$ at the roots.

- [The halving lemma](halving.md)
- [The two-torsion of a congruent number curve](two-torsion.md)

## Kernel and image over the rationals

- [Squarefree representatives of rational square classes](squarefree-representatives.md)
- [The kernel of the descent map over the rationals](descent-kernel.md)
- [The image of the descent map lies in the 2-Selmer group](descent-image.md)

## Positive rank gives every Selmer class

- [Counting $A/2A$](counting.md)
- [Positive rank and a Selmer group of order eight give every Selmer class (RK9)](every-selmer-class.md)
