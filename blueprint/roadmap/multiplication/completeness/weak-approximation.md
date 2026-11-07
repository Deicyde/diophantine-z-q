---
article_id: af_f97d1580e5ecd3f30a4dd17f
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.weak_approx_q
---

# Weak approximation for the parameter $q$

Let $S$ and $S'$ be disjoint finite sets of primes, $e_p\in\mathbb N$ for $p\in S$, $x_0\in\mathbb R$,
$\delta>0$, and $X\subset\mathbb R$ finite. Then there is $q\in\mathbb Q\setminus X$ with
$$v_p(q)\ge e_p\ (p\in S),\qquad v_p(q)\ge0\ (p\in S'),\qquad |q-x_0|<\delta .$$

In the completeness argument $S=S_b$ with $e_p=C_p$, $S'$ is the set of selected odd
contact primes of the slope, $x_0=R_0^{-1/2}$ is a real root of $1-R_0q^2$, and $X=\{\pm x_0\}$,
so that $a=1-R_0q^2$ is nonzero and arbitrarily small, and is a unit at $S_b$ and at the
selected primes.

**Proof sketch.** Put $M=\prod_{p\in S}p^{e_p}$ and choose a prime $\ell\notin S\cup S'$. The
numbers $Mn/\ell^k$ ($n\in\mathbb Z$, $k\in\mathbb N$) are dense in $\mathbb R$, and each satisfies the
valuation conditions because $\ell\notin S\cup S'$. Infinitely many of them lie in
$(x_0-\delta,x_0+\delta)$; choose one outside the finite set $X$.

## Depends on

None.

## Sources

- [Pole input of a completed slope](../../../sources/multiplication-locators.md#pole-input-of-a-completed-slope)
