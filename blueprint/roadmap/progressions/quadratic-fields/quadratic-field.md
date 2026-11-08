---
article_id: af_60c884c70a9f86fa477bbaad
declaration: def
origin: background
statement: formalized
lean: ZInQ.Progressions.Qsqrt, ZInQ.Progressions.Qsqrt.instNumberField, ZInQ.Progressions.Qsqrt.instCharZero, ZInQ.Progressions.Qsqrt.finrank, ZInQ.Progressions.Qsqrt.not_isSquare_of_squarefree, ZInQ.Progressions.Qsqrt.fact_not_isSquare, ZInQ.Progressions.Qsqrt.sqrtInt, ZInQ.Progressions.Qsqrt.sqrtInt_sq
---

# The quadratic field $\mathbb Q(\sqrt d)$

For an integer $d$, let $K_d=\mathbb Q(\sqrt d)=\mathbb Q[X]/(X^2-d)$ be the $\mathbb Q$-algebra
with basis $1,\sqrt d$ and $(\sqrt d)^2=d$. If $d$ is not the square of a rational number,
then $K_d$ is a number field of degree $[K_d:\mathbb Q]=2$, and $\sqrt d$ is an algebraic
integer of $K_d$ with square $d$. Every squarefree integer $d\ne1$ satisfies this hypothesis.

**Proof sketch.** If $d$ is not a rational square, $X^2-d$ is irreducible over $\mathbb Q$, so
the algebra is a field; it has characteristic $0$ and dimension $2$ over $\mathbb Q$, and
$\sqrt d$ is a root of the monic integer polynomial $X^2-d$. A squarefree $d\ne1$ is not the
square of a rational number ($d\ne0$, and $d=a^2/b^2$ in lowest terms forces $b=1$ and
$d=a^2$, so $d=1$).

## Depends on

None.

## Sources

- [Marcus, Chapter 2](../../../sources/progressions-locators.md#marcus-chapter-2)
