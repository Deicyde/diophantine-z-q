---
article_id: af_ab547664771091c0d84f11bb
---

# Character sums and $L$-values near $s=1$

Throughout, $q\ge1$, $\chi$ is a Dirichlet character modulo $q$, $\chi_0$ the principal one,
and $M=\log q+3$. For $\chi\ne\chi_0$ the $L$-function $L(s,\chi)$ is entire and equals
$\sum_{n\ge1}\chi(n)n^{-s}$ for $\mathrm{Re}\,s>1$. Every bound below is explicit, and the
value at $s=1$ is always reached as a limit from the right, never through a conditionally
convergent series.

## Summation by parts

A nonprincipal character sums to zero over every period, so its partial sums are bounded
by $q$; summation by parts against $n^{-\sigma}$ and $\log n\cdot n^{-\sigma}$ bounds the
tails.

- [Character sums are bounded by the modulus](character-sums.md)
- [Tails of the twisted harmonic sums](tails.md)

## Bounds to the right of $1$

For real $\sigma\ge1$, $L(\sigma,\chi)$ is at most $M$; for $\sigma>1$ its derivative is at
most $M^2$, so $L(\sigma,\chi)$ moves by at most $(\sigma-1)M^2$; the partial sums of
$\chi(n)/n$ approach $L(1,\chi)$ at rate $2q/x$ and those of $\chi(n)\log n/n$ stay below
$M^2$.

- [A bound for $L(\sigma,\chi)$ near $1$](l-value-bound.md)
- [Partial sums of $\chi(n)\log n/n$](log-partial-sums.md)
- [A bound for $L'(\sigma,\chi)$ to the right of $1$](derivative-bound.md)
- [Variation of $L(\sigma,\chi)$ near $1$](l-value-variation.md)
- [Partial sums of $\chi(n)/n$ approximate $L(1,\chi)$](partial-sums.md)

## Complex characters

For $\chi^2\ne\chi_0$ the inequality $|L^3(\cdot,\chi_0)L^4(\cdot,\chi)L(\cdot,\chi^2)|\ge1$
at $1+x$, with $x$ of size $M^{-9}$, turns these bounds into a lower bound for $|L(1,\chi)|$.

- [The principal $L$-function to the right of $1$](trivial-character.md)
- [A lower bound for $|L(1,\chi)|$ at complex characters](complex-lower-bound.md)
