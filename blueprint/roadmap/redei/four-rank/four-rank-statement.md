---
article_id: af_5b73705f8c8b4e09b8a2db80
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Redei.OddGClStatement
---

# The 4-rank statement

The *4-rank statement* is the following assertion. For every odd squarefree $n>1$, the genus
class number $g(n)$ is odd if and only if every $e\in\mathbb F_2^{T_n}$ with
$$\sum_{p\in T_n}R_{qp}\,e_p=0\quad\text{for every prime }q\mid n$$
is $0$ or $e_n$. Here $R$ is the Rédei matrix of $n$, and $e_n\in\mathbb F_2^{T_n}$ is $1$ at the
primes of $n$ and $0$ at $2$; it is the exponent vector of the ideal $(\sqrt{-n})$.

The hypothesis $n>1$ is needed. For $n=1$ the class group of $\mathbb Q(i)$ is trivial (a classical
fact), so $g(1)=1$ is odd. But $T_1=\{2\}$, the Rédei matrix has no rows and $e_1=0$, so the nonzero vector at $2$ is
killed by it.

## Depends on

- [The genus class number](../genus-class-number.md)
- [The Rédei matrix](../redei-matrix.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)

## Sources

- [Step 6: the 4-rank](../../../sources/redei-locators.md#step-6-the-4-rank)
- [Step 8: the bridge](../../../sources/redei-locators.md#step-8-the-bridge)
