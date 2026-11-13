---
article_id: af_d0b699b487389ac1d725c787
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.piZ, ZInQ.Contrib.HeckeFE.split_ne, ZInQ.Contrib.HeckeFE.norm_piZ, ZInQ.Contrib.HeckeFE.norm_conj_piZ, ZInQ.Contrib.HeckeFE.not_conj_dvd, ZInQ.Contrib.HeckeFE.prime_piZ, ZInQ.Contrib.HeckeFE.prime_conj_piZ, ZInQ.Contrib.HeckeFE.p_eq_mul, ZInQ.Contrib.HeckeFE.split_dvd, ZInQ.Contrib.HeckeFE.sum_normFiber_prime
---

# The Gaussian primes above a split prime

Notation of [Gaussian integers as pairs](norm-fibres.md): $A_n$ is the set of Gaussian integers of
norm $n$ and $U$ the set of the four units.

Let $p\equiv1\pmod4$ be prime and $a,b$ natural numbers with $a^2+b^2=p$; put $\pi=a+bi$. Then:
(a) $a\ne0$, $b\ne0$ and $a\ne b$; (b) $N(\pi)=N(\bar\pi)=p$; (c) $\bar\pi\nmid\pi$; (d) $\pi$ and
$\bar\pi$ are prime elements of $\mathbb Z[i]$; (e) $p=\pi\bar\pi$; (f) every
$\gamma\in\mathbb Z[i]$ with $p\mid N(\gamma)$ is divisible by $\pi$ or by $\bar\pi$, and by both
exactly when $p\mid\gamma$; (g) for every $f:\mathbb Z^2\to\mathbb C$,
$$\sum_{\alpha\in A_p}f(\alpha)=\sum_{e\in U}f(e\pi)+\sum_{e\in U}f(e\bar\pi).$$

**Proof sketch.** (a) $a=0$ or $b=0$ makes $p$ a square; $a=b$ makes $p=2a^2$ even. (b), (e) Direct. (c) If
$\bar\pi\mid\pi$, equal norms make the quotient a unit; each of the four units contradicts (a). (d)
By [norm fibres at primes](norm-fibres-primes.md) (3). (f) $\pi$ divides $p\mid N(\gamma)=\gamma\bar\gamma$, so $\pi\mid\gamma$ or
$\pi\mid\bar\gamma$, the latter meaning $\bar\pi\mid\gamma$. If both divide $\gamma$, then, being
non-associate primes by (c), their product $p$ does; the converse is (e). (g) By (f) every element
of $A_p$ is $e\pi$ or $e\bar\pi$ with $N(e)=1$, so $e\in U$; the two sets $U\pi$ and $U\bar\pi$ are
disjoint by (c), and $e\mapsto e\pi$ is injective.

## Depends on

- [Gaussian integers as pairs, norms and units](norm-fibres.md)

## Proof depends on

- [Gaussian integers whose norm is a prime power](norm-fibres-primes.md)

## Sources

- [Arithmetic of the Gaussian integers](../../../../../sources/hecke-locators.md#arithmetic-of-the-gaussian-integers)
