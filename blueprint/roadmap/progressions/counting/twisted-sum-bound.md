---
article_id: af_4242ba899937af50d65010fc
declaration: theorem
origin: background
---

# The twisted sum and $L(1,\chi)$

Let $q\ge1$, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, put $M=\log q+3$,
and for real $x$ let
$$S_\chi(x)=\sum_{n\le x}\frac{\chi(n)\Lambda(n)}{n}.$$
Then for every real $x\ge1$,
$$|L(1,\chi)|\,|S_\chi(x)|\le M^2+12q .$$

**Proof sketch.** Write $\log n=\sum_{d\mid n}\Lambda(d)$ and $n=dm$, using
$\chi(dm)=\chi(d)\chi(m)$:
$$T(x):=\sum_{n\le x}\frac{\chi(n)\log n}{n}
=\sum_{d\le x}\frac{\chi(d)\Lambda(d)}{d}\sum_{m\le x/d}\frac{\chi(m)}{m}
=L(1,\chi)S_\chi(x)+\sum_{d\le x}\frac{\chi(d)\Lambda(d)}{d}R\Bigl(\frac xd\Bigr),$$
where $R(y)=\sum_{m\le y}\chi(m)/m-L(1,\chi)$ satisfies $|R(y)|\le2q/y$ for $y\ge1$. So
$|L(1,\chi)||S_\chi(x)|\le|T(x)|+(2q/x)\sum_{d\le x}\Lambda(d)=|T(x)|+2q\psi(x)/x$, and
$|T(x)|\le M^2$ while $\psi(x)\le(\log4+4)x\le6x$.

## Depends on

None.

## Proof depends on

- [Partial sums of $\chi(n)/n$ approximate $L(1,\chi)$](../lseries/partial-sums.md)
- [Partial sums of $\chi(n)\log n/n$](../lseries/log-partial-sums.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
- [Apostol, Chapter 4](../../../sources/progressions-locators.md#apostol-chapter-4)
