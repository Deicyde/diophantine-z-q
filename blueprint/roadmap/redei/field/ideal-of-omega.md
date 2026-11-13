---
article_id: af_0ed1181e9cbfc97dc4b11348
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.span_omega, ZInQ.RouteK.Redei.omegaO_mem_ramIdeal
---

# The ideal $(\sqrt{-n})$ is the product of the ramified odd primes

Let $n$ be odd and squarefree. Then
$$(\omega)=\prod_{p\mid n}\mathfrak p_p$$
in $\mathcal O$, the product over the primes $p$ dividing $n$. This rests on the following, for
every $n\ge1$: if $p$ is a prime dividing $n$, then $\omega\in\mathfrak p_p$.

**Proof sketch.** For a prime $p\mid n$, $\omega^2=-n$ lies in $\mathfrak p_p$, which contains $p$,
and $\mathfrak p_p$ is prime, so $\omega\in\mathfrak p_p$; that is, $\mathfrak p_p$ divides
$(\omega)$. For distinct primes $p,q\mid n$ the maximal ideals $\mathfrak p_p$ and $\mathfrak p_q$
are distinct (if they were equal, $q\in\mathfrak p_p$ would give $p\mid q$), so they are pairwise
coprime, and their product divides $(\omega)$. The norms agree:
$\prod_{p\mid n}N(\mathfrak p_p)=\prod_{p\mid n}p=n=N(\omega)\ne0$, as $n$ is squarefree. An ideal
dividing an ideal of the same nonzero norm equals it.

## Depends on

- [The ramified primes and the ideals $\mathfrak p_p$](ramified-primes.md)
- [Integers and norms of $\mathbb Q(\sqrt{-n})$](integers-and-norms.md)

## Proof depends on

- [The primes of the discriminant ramify](ramified-prime-ideals.md)
- [Split, inert and ramified primes](prime-trichotomy.md)

## Sources

- [Step 2: primes](../../../sources/redei-locators.md#step-2-primes)
