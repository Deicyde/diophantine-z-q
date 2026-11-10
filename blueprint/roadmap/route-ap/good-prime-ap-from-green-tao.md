---
article_id: af_e138ccfd67060a15d34203cb
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.goodPrimeAP_of_greenTaoDense
---

# 22P_AP from Green–Tao and Proposition D

Assume Szemerédi's theorem in the primes (every set of primes of positive relative upper density
contains arithmetic progressions of every finite length) and that the good slope primes have
positive relative upper density in the primes. Then 22P_AP holds.

Both assumptions are theorems here ([Szemerédi's theorem in the primes](../green-tao/dense-theorem.md),
[Proposition D](../density/proposition-d.md)), so 22P_AP holds unconditionally.

**Proof sketch.** Let $M=\max S_b$ and $G'$ the set of good slope primes larger than $M$. The good
slope primes up to $N$ number at most $|G'\cap[0,N]|+M+1$. If $\delta\pi(N)$ is at most the number
of good slope primes up to $N$ for infinitely many $N$, then, since $\pi(N)\to\infty$,
$M+1\le(\delta/2)\pi(N)$ for all large $N$, and $(\delta/2)\pi(N)\le|G'\cap[0,N]|$ for infinitely
many $N$. So $G'$ is a set of primes of positive relative upper density, and Szemerédi's theorem
in the primes gives, for every $K$, a progression $a+bj$ ($j\le K$, $b\ge1$) in $G'$; its first
term is a prime, so $a\ge1$.

## Depends on

- [Szemerédi's theorem in the primes: the statement](../green-tao/dense-form.md)
- [The density of good slope primes: the statement](../density/good-prime-density.md)
- [The statement 22P_AP: long progressions of good slope primes](good-prime-ap.md)

## Sources

- [Green–Tao implies 22P_AP](../../sources/route-ap-locators.md#greentao-implies-22p_ap)
- [Green–Tao 2008](../../sources/route-ap-locators.md#greentao-2008)
