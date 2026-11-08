---
article_id: af_610b61cb31c5ec6a071c67ce
declaration: theorem
origin: background
---

# Twenty-two primes from a twisted sum bound

Let $q\ge1$ and $B\ge0$ be such that
$\bigl|\sum_{n\le t}\chi(n)\Lambda(n)/n\bigr|\le B$ for every nonprincipal Dirichlet character
$\chi$ modulo $q$ and every real $t\ge1$. Let $a$ be an integer coprime to $q$, and let
$1\le y\le x$ be real with
$$\log\frac xy\ge q\,(2B+11)+12+\log q .$$
Then at least $22$ primes $p\equiv a\pmod q$ satisfy $y<p\le x$.

**Proof sketch.** Let $\Sigma=\sum_{y<n\le x,\ n\equiv a}\Lambda(n)/n$. Detecting the
class by characters,
$\varphi(q)\Sigma=\sum_\chi\overline{\chi(a)}\sum_{y<n\le x}\chi(n)\Lambda(n)/n$. The
principal character contributes at least $\log(x/y)-12-\log q$, and each of the other
$\varphi(q)-1$ characters at most $2B$ in absolute value. Since
$\log(x/y)-12-\log q\ge q(2B+11)\ge\varphi(q)(2B+11)$, this gives $\Sigma\ge11$. On the
other hand, if at most $21$ primes $p\equiv a$ lie in $(y,x]$, then, as $\log p/p\le1/e$
and the higher prime powers contribute at most $3$, $\Sigma\le21/e+3<11$.

## Depends on

None.

## Proof depends on

- [Detecting a residue class by characters](orthogonality.md)
- [The principal character](principal-character.md)
- [Higher prime powers contribute little](prime-powers.md)

## Sources

- [Apostol, Chapter 7](../../../sources/progressions-locators.md#apostol-chapter-7)
