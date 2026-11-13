---
article_id: af_0090dc69dc59a654c2e9bbc9
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.ramIdeal_spec, ZInQ.RouteK.Redei.mem_span_of_mul_self_mem, ZInQ.RouteK.Redei.ramified_of_dvd, ZInQ.RouteK.Redei.ramified_two, ZInQ.RouteK.Redei.ramIdeal_sq, ZInQ.RouteK.Redei.eq_ramIdeal_of_liesOver, ZInQ.RouteK.Redei.smul_ramIdeal
---

# The primes of the discriminant ramify

Let $n$ be odd and squarefree and $p\in T_n$. Then $\mathfrak p_p$ is maximal,
$\mathfrak p_p^2=p\mathcal O$ and $N(\mathfrak p_p)=p$. Moreover $\mathfrak p_p$ is the only prime
ideal of $\mathcal O$ lying over $p$, and every automorphism of $K$ fixes $\mathfrak p_p$.

These rest on the following, for $n\ge1$:

- if $n$ is squarefree and $p$ is a prime dividing $n$, every maximal ideal $P$ over $p$ has
  $P^2=p\mathcal O$;
- if $n\equiv1\pmod4$, every maximal ideal $P$ over $2$ has $P^2=2\mathcal O$;
- if $P$ is a maximal ideal over a prime $p$ with $P^2\ne p\mathcal O$, then for $x\in\mathcal O$,
  $x^2\in p\mathcal O$ implies $x\in p\mathcal O$.

**Proof sketch.** For the last item, $P$ is split or inert. If it is split, $x$ lies in the prime
ideals $P$ and $\sigma P$, which both contain $p\mathcal O$; they are distinct maximal ideals, so
coprime, and $x\in P\cap\sigma P=P\cdot\sigma P=p\mathcal O$. If it is inert, $p\mathcal O=P$ is
prime.

- For $p\mid n$: $\omega^2=-n\in p\mathcal O$. If $P^2\ne p\mathcal O$, then $\omega=py$, and taking
  norms gives $n=p^2N(y)$, contradicting squarefreeness.
- For $n=4c+1$: $(1+\omega)^2=2(\omega-2c)\in2\mathcal O$. If $P^2\ne2\mathcal O$, then
  $1+\omega=2y$, and taking norms gives $1+n=4N(y)$, but $1+n=4c+2$.

An element $p\in T_n$ divides $n$, or is $2$ with $n\not\equiv3\pmod4$, that is, with
$n\equiv1\pmod4$ as $n$ is odd. So $\mathfrak p_p^2=p\mathcal O$, and then $N(\mathfrak p_p)=p$. A
prime ideal $Q$ over $p$ contains $p\mathcal O=\mathfrak p_p^2$, so it contains the maximal ideal
$\mathfrak p_p$ and equals it. For an automorphism $\tau$,
$\mathfrak p_p^2=p\mathcal O\subseteq\tau\mathfrak p_p$, so $\tau\mathfrak p_p=\mathfrak p_p$.

## Depends on

- [The ramified primes and the ideals $\mathfrak p_p$](ramified-primes.md)
- [The conjugation of $\mathbb Q(\sqrt{-n})$](conjugation.md)

## Proof depends on

- [Split, inert and ramified primes](prime-trichotomy.md)
- [Ramified primes divide the discriminant](ramified-primes-divide.md)
- [Integers and norms of $\mathbb Q(\sqrt{-n})$](integers-and-norms.md)

## Sources

- [Step 2: primes](../../../sources/redei-locators.md#step-2-primes)
