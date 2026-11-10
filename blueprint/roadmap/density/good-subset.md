---
article_id: af_a73d0087272746b2731488aa
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.goodSlopePrime_of_mem_CL, ZInQ.Density.BadSet, ZInQ.Density.TL, ZInQ.Density.badSet_eq, ZInQ.Density.cp_rep, ZInQ.Density.TL_subset_primes, ZInQ.Density.goodSlopePrimes_subset_primes
---

# A subset of good slope primes

For a prime $\ell$ let $\mathrm{Bad}_\ell$ be the set of primes $p$ in the class ($p\equiv1\pmod8$,
$(p/7)=-1$) with $\ell\mid c_p$ and $\ell\mid p+1$, and for $L\ge1$ let $T_L$ be the union of the
$\mathrm{Bad}_\ell$ over the primes $\ell>L$ with $\ell\equiv1\pmod4$. Then every prime of
$G^*_L=C_L\setminus T_L$ is a good slope prime.

**Proof sketch.** Let $p\in C_L\setminus T_L$; it is in the class. If $\gcd(c_p,p+1)\ne1$, take a prime
$\ell$ dividing it. Then $\ell$ is odd (since $c_p$ is odd), so $\ell\equiv1\pmod4$
and hence $\ell\ge5$. If $\ell\le L$ then $\ell\in Q_L$, which is impossible since $\ell\mid p+1$;
so $\ell>L$ and $p\in\mathrm{Bad}_\ell\subseteq T_L$, a contradiction. Hence
$\gcd(c_p,p+1)=1$, and $p$ is a good slope prime by the description.

## Depends on

- [The description of the good slope primes](description.md)
- [The residue set $A_L$ and the primes $C_L$](residue-set.md)

## Sources

- [The residue set](../../sources/density-locators.md#the-residue-set)
