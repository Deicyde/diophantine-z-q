---
article_id: af_3b26e30205410b95d79b7bc0
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.GaussSieve.siftedSum_le, ZInQ.Density.GaussSieve.gaussSieve, ZInQ.Density.GaussSieve.gsPrimes, ZInQ.Density.GaussSieve.gsProd, ZInQ.Density.GaussSieve.gsNu, ZInQ.Density.GaussSieve.gsBox, ZInQ.Density.GaussSieve.gsF, ZInQ.Density.GaussSieve.selbergTerms_prime_eq, ZInQ.Density.GaussSieve.selbergBoundingSum_ge_log, ZInQ.Density.GaussSieve.errSum_le, ZInQ.Density.GaussSieve.abs_rem_le, ZInQ.Density.siftedSum_le_five
---

# The sieve for the primes bad at $\ell$

Let $\ell$ be a prime, $b$ an integer, $K\ge0$ and $w\ge1$. Sift the values of
$F(U,V)=(\ell U)^2+(b+\ell V)^2$ on the box $\mathcal B=[-K,K]\times[-K-1,K]$, each counted with its
multiplicity, by the primes $q\le w$ with $q\equiv1\pmod4$ and $q\ne\ell$, with density
$\nu(q)=(2q-1)/q^2$ and level $w^2$; the total mass is $X=(2K+1)(2K+2)$. Then the number of points of
$\mathcal B$ whose value is coprime to all these primes is at most
$$\frac XS+w^8(4K+4),$$
where $S$ is the Selberg sum of the sieve, and $S\ge(\log w)/10$ if $\ell\ge5$.

**Proof sketch.** The Selberg sieve bound. By the local densities, $\rho(d)=\nu(d)d^2$ for $d\mid P$, so
the box count bounds each remainder by $|R_d|\le d^2(4K+4)$ for $d\mid P$; with $3^{\omega(d)}\le d$
(the prime factors of $d$ are at least $5$) the error sum is at most
$\sum_{d\le w^2}d^3(4K+4)\le w^8(4K+4)$. At a sifting prime
$g(q)=(2q-1)/(q-1)^2=(1-1/q)^{-2}-1$, so the lower bound for the Selberg sum applies:
$S\ge\sum_{m\le w,\ \mathrm{rad}(m)\mid P}\tau(m)/m$, which is the sum of $h$ over $m\le w$ prime to
$\ell$, at least $(1-2/\ell)(\log w)/6\ge(\log w)/10$ for $\ell\ge5$.

## Depends on

- [The Selberg sieve bound](selberg-sieve.md)

## Proof depends on

- [Local densities of $(\ell U)^2+(b+\ell V)^2$](local-densities.md)
- [Counting a box with a divisibility condition](box-count.md)
- [A lower bound for the Selberg sum](selberg-sum.md)

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
