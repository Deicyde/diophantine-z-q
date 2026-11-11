---
article_id: af_724e95612af722e472b92e2b
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Redei.ramSet, ZInQ.RouteK.Redei.ramIdeal, ZInQ.RouteK.Redei.exists_maximal_liesOver, ZInQ.RouteK.Redei.ramIdeal_isMaximal, ZInQ.RouteK.Redei.ramIdeal_liesOver, ZInQ.RouteK.Redei.prime_of_mem_ramSet, ZInQ.RouteK.Redei.ramIdeal_ne_bot, ZInQ.RouteK.Redei.ramIdeal_mem, ZInQ.RouteK.Redei.mem_ramSet_of_mem_primeFactors
---

# The ramified primes and the ideals $\mathfrak p_p$

For a natural number $n$, let $T_n$ be the set of prime factors of $n$ (empty for $n=0$) if
$n\equiv3\pmod4$, and that set together with $2$ otherwise; write $t=|T_n|$. Every element of
$T_n$ is prime, and every prime factor of $n$ lies in $T_n$. Motivation: for odd squarefree $n$,
$T_n$ is the set of primes dividing the discriminant of $\mathbb Q(\sqrt{-n})$, and these are
exactly the primes that ramify there.

Now let $n\ge1$ and let $\mathcal O$ be the ring of integers of $K=\mathbb Q(\sqrt{-n})$. Every
prime $p$ has a maximal ideal of $\mathcal O$ lying over it, since $\mathcal O$ is integral over
$\mathbb Z$. For a prime $p$, $\mathfrak p_p$ denotes a fixed choice of a maximal ideal of
$\mathcal O$ lying over $p$; for $p$ not prime, $\mathfrak p_p=\mathcal O$. Thus for every prime
$p$ the ideal $\mathfrak p_p$ is maximal and lies over $p$, and $\mathfrak p_p\ne0$ for every
natural number $p$.

## Depends on

- [The genus class number](../genus-class-number.md)
- [Split, inert and ramified primes](prime-trichotomy.md)

## Sources

- [Step 2: primes](../../../sources/redei-locators.md#step-2-primes)
