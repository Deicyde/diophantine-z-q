---
article_id: af_7e470611094c7ff7e7dfd39d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.mem_range_psi_of_conj_eq, ZInQ.RouteK.Redei.ambig_exists_dvd, ZInQ.RouteK.Redei.ambig_two_mem_ramSet
---

# Classes of invariant ideals are ambiguous

Let $n$ be odd and squarefree, $\sigma$ the nontrivial automorphism of $\mathbb Q(\sqrt{-n})$ and
$I$ a nonzero ideal of $\mathcal O$ with $\sigma I=I$. Then $[I]$ lies in the image of $\psi$.

Along the way:

- for $n$ odd and squarefree, every nonzero ideal $J\ne\mathcal O$ with $\sigma J=J$ is divisible
  by a nonzero ideal $Q\ne\mathcal O$ with $\sigma Q=Q$ whose class lies in the image of $\psi$;
- for every $n$ with $n\equiv1\pmod4$, $2\in T_n$.

**Proof sketch.** For the divisor: take a maximal ideal $P\supseteq J$; it is nonzero, so it lies
over a prime $p$.

- If $P$ is split, then $J=\sigma J\subseteq\sigma P$, so $J\subseteq P\cap\sigma P=P\cdot\sigma P=p\mathcal O$.
  Take $Q=p\mathcal O$, which is $\sigma$-stable and principal, of class $1$.
- If $P$ is inert, take $Q=P=p\mathcal O$, again of class $1$.
- If $P$ is ramified, then $p\mid n$, or $p=2$ and $n\equiv1\pmod4$; in both cases $p\in T_n$, so
  $P=\mathfrak p_p$ is the only prime over $p$. Take $Q=P$, which is $\sigma$-stable, with class
  $[\mathfrak p_p]=\psi(\delta_p)$.

Then argue by strong induction on $N(I)$. If $I=\mathcal O$, its class is $1$. Otherwise
$I=QJ$ with $Q$ as above; cancelling $Q=\sigma Q$ in $Q\,\sigma J=QJ$ gives $\sigma J=J$, and
$N(J)<N(I)$ since $N(Q)\ge2$. So $[I]=[Q][J]$ lies in the image of $\psi$.

## Depends on

- [The ambiguous class map $\psi$](ambiguous-class-map.md)
- [The conjugation of $\mathbb Q(\sqrt{-n})$](../field/conjugation.md)

## Proof depends on

- [Split, inert and ramified primes](../field/prime-trichotomy.md)
- [Ramified primes divide the discriminant](../field/ramified-primes-divide.md)
- [The primes of the discriminant ramify](../field/ramified-prime-ideals.md)
- [The classes of the ramified primes](ramified-classes.md)

## Sources

- [Step 3: ambiguous classes](../../../sources/redei-locators.md#step-3-ambiguous-classes)
