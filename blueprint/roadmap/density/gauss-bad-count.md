---
article_id: af_42be121b4f82460900f77cc2
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.card_gaussBad_le, ZInQ.Density.GaussBad, ZInQ.Density.mem_gaussBad_of_bad, ZInQ.Density.card_sqrt_neg_one_le, ZInQ.Density.mem_support_of_gaussBad, ZInQ.Density.card_support_primes_le_siftedSum
---

# The count of primes $c^2+e^2$ with $\ell\mid c$ and $\ell\mid p+1$

For a prime $\ell$ let $\mathrm{GB}_\ell$ be the set of primes $p=c^2+e^2$ ($c,e\in\mathbb Z$) with
$\ell\mid c$ and $\ell\mid p+1$; by the description it contains $\mathrm{Bad}_\ell$. Let $\ell\ge5$,
$N\ge0$, $w\ge2$ and $K=\lfloor\lfloor\sqrt N\rfloor/\ell\rfloor$. Then
$$\#\bigl(\mathrm{GB}_\ell\cap[0,N]\bigr)\le(w+1)+2\Bigl(\frac{10(2K+1)(2K+2)}{\log w}+w^8(4K+4)\Bigr).$$

**Proof sketch.** For $p\in\mathrm{GB}_\ell\cap[0,N]$, $c=\ell U$ and $e^2\equiv-1\pmod\ell$, so
$e\equiv b\pmod\ell$ for one of the at most two roots $b$ of $b^2\equiv-1$, and $e=b+\ell V$ (after
choosing the sign of $e$ and $b\in[0,\ell)$) with $(U,V)$ in the box $[-K,K]\times[-K-1,K]$; distinct
primes give distinct points. A prime $p>w$ is coprime to every sifting prime, so all but at most
$w+1$ of these primes are counted by the sifted sum of the sieve for the primes bad at $\ell$; apply
its bound, with $S\ge(\log w)/10$, for each root $b$.

## Depends on

- [A subset of good slope primes](good-subset.md)

## Proof depends on

- [The description of the good slope primes](description.md)
- [The sieve for the primes bad at $\ell$](sieve-instance.md)

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
