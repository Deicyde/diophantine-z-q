---
article_id: af_517b72bb2aa877d83ed4c2b0
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.exists_absNorm_eq_of_isSquare
---

# Split primes

Let $n\ge1$, $\mathcal O$ the ring of integers of $\mathbb Q(\sqrt{-n})$, and $p$ an odd prime
with $p\nmid n$ such that $-n$ is a square modulo $p$. Then $\mathcal O$ has a nonzero ideal of
norm $p$.

**Proof sketch.** Take a maximal ideal $P$ over $p$; it is nonzero. If $P$ is split, $N(P)=p$. It
is not ramified, since a ramified prime divides $n$ or is $2$. It is not inert either: if
$P=p\mathcal O$ and $m^2\equiv-n\pmod p$, then $(m+\omega)(m-\omega)=m^2+n\in P$. As $P$ is prime
and $\sigma$-stable, and $\sigma$ exchanges the two factors, both lie in $P$, so their sum
$2m\in P\cap\mathbb Z=p\mathbb Z$. As $p$ is odd, $p\mid m$, and then $p\mid(m^2+n)-m^2=n$, a
contradiction.

## Depends on

- [The genus class number](../genus-class-number.md)

## Proof depends on

- [Split, inert and ramified primes](../field/prime-trichotomy.md)
- [Ramified primes divide the discriminant](../field/ramified-primes-divide.md)
- [The conjugation of $\mathbb Q(\sqrt{-n})$](../field/conjugation.md)
- [Integers and norms of $\mathbb Q(\sqrt{-n})$](../field/integers-and-norms.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)

## Sources

- [Step 5: Dirichlet's theorem](../../../sources/redei-locators.md#step-5-dirichlets-theorem)
