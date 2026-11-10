---
article_id: af_e5c4edb7505bfccc5f647a96
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.GaussSieve.selbergBoundingSum_ge_tau, ZInQ.Density.GaussSieve.prod_factors_sum_pow_mult, ZInQ.Density.GaussSieve.tauDiv, ZInQ.Density.GaussSieve.rSum, ZInQ.Density.GaussSieve.rSum_ge_log, ZInQ.Density.GaussSieve.hDiv, ZInQ.Density.GaussSieve.vDiv, ZInQ.Density.GaussSieve.hSum, ZInQ.Density.GaussSieve.rDiv_eq_hDiv_mul_vDiv, ZInQ.Density.GaussSieve.vSum_le_four, ZInQ.Density.GaussSieve.log_le_hSum, ZInQ.Density.GaussSieve.hSum_coprime_ge
---

# A lower bound for the Selberg sum

Let a Selberg sieve have level $w^2$ ($w\ge1$) and satisfy $g(q)\ge(1-1/q)^{-2}-1$ at the primes
$q\mid P$. Then its Selberg sum satisfies
$$S\ge\sum_{\substack{m\le w\ \mathrm{rad}(m)\mid P}}\frac{\tau(m)}m,$$
where $\tau$ is the number of divisors. Moreover, with $r(n)=\sum_{d\mid n}\chi_4(d)$ and
$h(n)=\tau(n)/n$ if every prime factor of $n$ is $\equiv1\pmod4$, $h(n)=0$ otherwise:

1. $\sum_{n\le w}r(n)/n\ge\frac23\log w$;
2. $\log w\le6\sum_{n\le w}h(n)$;
3. for a prime $\ell$, removing the multiples of $\ell$ keeps at least the fraction $1-2/\ell$:
   $\sum_{n\le w,\ \ell\nmid n}h(n)\ge(1-2/\ell)\sum_{n\le w}h(n)$.

**Proof sketch.** Expand $g(q)\ge\sum_{k\ge1}(k+1)q^{-k}$ multiplicatively: for $l\mid P$ with $l\le w$,
$g(l)$ dominates the sum of $\tau(m)/m$ over the $m\le w$ with radical $l$. (1) Write
$\sum_{n\le w}r(n)/n=\sum_d(\chi_4(d)/d)H(\lfloor w/d\rfloor)$ and pair the terms $d\equiv1,3\pmod4$
in blocks; no Euler constant is needed. (2) $r(n)/n$ is the Dirichlet convolution of $h$ with a
nonnegative function $v$ supported on numbers without prime factors $\equiv1\pmod4$, whose partial
sums are at most $4$; so $\sum r(n)/n\le4\sum h(n)$. (3) $h(\ell m)\le2h(m)/\ell$.

## Depends on

- [The Selberg sieve bound](selberg-sieve.md)

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
