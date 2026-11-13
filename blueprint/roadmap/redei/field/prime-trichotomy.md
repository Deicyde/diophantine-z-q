---
article_id: af_43e294603cc158e1874428a8
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.prime_trichotomy, ZInQ.RouteK.Redei.absNorm_span_natCast_eq, ZInQ.RouteK.Redei.span_natCast_isPrime, ZInQ.RouteK.Redei.natCast_mem_of_liesOver, ZInQ.RouteK.Redei.span_le_of_liesOver, ZInQ.RouteK.Redei.intCast_mem_iff_of_liesOver, ZInQ.RouteK.Redei.liesOver_of_natCast_mem, ZInQ.RouteK.Redei.exists_prime_liesOver, ZInQ.RouteK.Redei.natCast_ne_zero_O, ZInQ.RouteK.Redei.ne_bot_of_liesOver, ZInQ.RouteK.Redei.smul_natCast_O, ZInQ.RouteK.Redei.smul_intCast_O, ZInQ.RouteK.Redei.smul_span_natCast, ZInQ.RouteK.Redei.span_le_smul_of_liesOver, ZInQ.RouteK.Redei.smul_ne_bot, ZInQ.RouteK.Redei.smul_isMaximal, ZInQ.RouteK.Redei.smul_eq_of_pow_le, ZInQ.RouteK.Redei.eq_of_dvd_of_absNorm_eq
---

# Split, inert and ramified primes

Let $n\ge1$, $\mathcal O$ the ring of integers of $K=\mathbb Q(\sqrt{-n})$ and $\sigma$ the
nontrivial automorphism. An ideal $P$ of $\mathcal O$ *lies over* $p$ if
$P\cap\mathbb Z=p\mathbb Z$. Let $p$ be a prime and $P$ a maximal ideal of $\mathcal O$ lying over
$p$. Then one of the following holds:

- *split*: $\sigma P\ne P$, $P\cdot\sigma P=p\mathcal O$ and $N(P)=p$;
- *inert*: $\sigma P=P$, $P=p\mathcal O$ and $N(P)=p^2$;
- *ramified*: $\sigma P=P$, $P^2=p\mathcal O$ and $N(P)=p$.

Along the way, with $\tau$ any automorphism of $K$ acting on the ideals of $\mathcal O$:

- $N(m\mathcal O)=m^2$ for every natural number $m$, and $m\ne0$ in $\mathcal O$ for $m\ne0$;
- an ideal $P$ over $p$ contains $p$, so $p\mathcal O\subseteq P$ and $p\mathcal O\subseteq\tau P$;
  an integer lies in $P$ if and only if $p$ divides it; and for $p$ prime, $P\ne0$;
- $p\mathbb Z$ is a prime ideal of $\mathbb Z$, a prime ideal of $\mathcal O$ containing $p$ lies
  over $p$, and every nonzero prime ideal of $\mathcal O$ lies over some prime;
- $\tau$ fixes every integer and every ideal $m\mathcal O$, and sends nonzero ideals to nonzero
  ideals and maximal ideals to maximal ideals;
- a maximal ideal $P$ with $P^k\subseteq\tau P$ for some $k$ satisfies $\tau P=P$;
- if $I$ divides $J$ and $N(I)=N(J)\ne0$, then $I=J$.

**Proof sketch.** Since $p\mathcal O\subseteq P$, write $p\mathcal O=PM$. Then
$N(P)N(M)=N(p\mathcal O)=p^2$, and $N(P)\ne1$ because $P\ne\mathcal O$.

- If $N(P)=p^2$, then $N(M)=1$, so $M=\mathcal O$ and $P=p\mathcal O$. As
  $p\mathcal O\subseteq\sigma P$, the maximal ideal $P$ is contained in $\sigma P$, so
  $\sigma P=P$: inert.
- If $N(P)=p$, then $N(M)=p$ is prime, so $M$ is a prime ideal; it contains $p$, so it lies over
  $p$. The automorphisms act transitively on the primes over $p$, so $M=\tau P$ with $\tau=1$ or
  $\tau=\sigma$.
  - If $M=P$, then $P^2=p\mathcal O\subseteq\sigma P$, so $\sigma P=P$: ramified.
  - If $M=\sigma P$, the case $\sigma P=P$ is ramified and the case $\sigma P\ne P$ is split.

Only norms of ideals and the transitivity of the Galois action are used, not ramification
indices.

## Depends on

- [The conjugation of $\mathbb Q(\sqrt{-n})$](conjugation.md)

## Proof depends on

- [Integers and norms of $\mathbb Q(\sqrt{-n})$](integers-and-norms.md)

## Sources

- [Step 2: primes](../../../sources/redei-locators.md#step-2-primes)
