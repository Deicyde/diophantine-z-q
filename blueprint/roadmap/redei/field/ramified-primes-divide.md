---
article_id: af_ca9c7825ffd1bc5f4306747f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.dvd_of_ramified, ZInQ.RouteK.Redei.absNorm_of_ramified, ZInQ.RouteK.Redei.exists_int_sub_mem_of_absNorm, ZInQ.RouteK.Redei.sub_conj_mem, ZInQ.RouteK.Redei.conj_thetaO
---

# Ramified primes divide the discriminant

Let $n\ge1$, $\mathcal O$ the ring of integers of $K=\mathbb Q(\sqrt{-n})$, $p$ a prime and $P$
a maximal ideal of $\mathcal O$ lying over $p$ with $P^2=p\mathcal O$. Then $p\mid n$, or $p=2$
and $n\equiv1\pmod4$.

Along the way:

- an ideal $P$ with $P^2=p\mathcal O$ has $N(P)=p$;
- if $P$ is maximal and $N(P)=p$ is prime, every element of $\mathcal O$ is congruent modulo $P$
  to an integer;
- if moreover $\tau P=P$ for an automorphism $\tau$ of $K$, then $x-\tau(x)\in P$ for every
  $x\in\mathcal O$;
- for $n\equiv3\pmod4$, the element $\theta=(1+\omega)/2$ of $\mathcal O$ satisfies $\sigma(\theta)=1-\theta$,
  where $\sigma$ is the nontrivial automorphism.

**Proof sketch.** $P^2=p\mathcal O\subseteq\sigma P$, so $\sigma P=P$; and $N(P)^2=N(p\mathcal O)=p^2$,
so $N(P)=p$. Then $\mathcal O/P$ has $p$ elements, so $\mathbb Z\to\mathcal O/P$ is onto: every
$x$ is congruent to an integer $m$ modulo $P$, and so is $\sigma(x)$, since $\sigma$ fixes $m$ and
$P$. Hence $x-\sigma(x)\in P$.

- With $x=\omega$: $2\omega\in P$, so $-4n=(2\omega)^2\in P\cap\mathbb Z=p\mathbb Z$ and $p\mid4n$.
  If $p\nmid n$, then $p=2$ and $n$ is odd.
- If $p=2\nmid n$ and $n\equiv3\pmod4$, take $x=\theta$: $\theta-(1-\theta)=2\theta-1=\omega\in P$.
  Then $-n=\omega^2\in P\cap\mathbb Z=2\mathbb Z$, a contradiction. So $n\equiv1\pmod4$.

## Depends on

- [The genus class number](../genus-class-number.md)
- [The conjugation of $\mathbb Q(\sqrt{-n})$](conjugation.md)
- [Integers and norms of $\mathbb Q(\sqrt{-n})$](integers-and-norms.md)
- [Split, inert and ramified primes](prime-trichotomy.md)

## Sources

- [Step 2: primes](../../../sources/redei-locators.md#step-2-primes)
