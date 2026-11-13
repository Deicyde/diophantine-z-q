---
article_id: af_ea09b200a2b7c441df8e8645
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.goodSlopePrime_iff, ZInQ.Density.InClass, ZInQ.Density.cp, ZInQ.Density.cp_odd, ZInQ.Density.exists_sq_add_sq, ZInQ.Density.sq_add_sq_of_nonsquare, ZInQ.Density.pointCount_pair, ZInQ.Density.gcd_pointCount_eq, ZInQ.Density.goodSlopePrime_of_gcd, ZInQ.Density.mod_four_of_dvd_cp, ZInQ.Density.d_mul_dbar, ZInQ.Density.int_gcd_sub_add_two_mul, ZInQ.Density.goodSlopePrime_seventeen'
---

# The description of the good slope primes

Say that a prime $p$ is *in the class* if $p\equiv1\pmod8$ and $p\bmod7\in\{3,5,6\}$ (that is,
$(p/7)=-1$), and put $c_p=\varphi_p(1)/2$. Let $p$ be a prime in the class. Then:

1. $c_p$ is odd, and $p=c_p^2+e_p^2$ with $e_p=\varphi_p(r_0)/2$ for any non-square $r_0$;
2. for every $r\in\mathbb F_p$ with $r^2=2$, the point counts of $y^2=x^3-(75-53r)^2x$ and
   $y^2=x^3-(75+53r)^2x$ over $\mathbb F_p$ are $p+1-2c_p$ and $p+1+2c_p$, in some order;
3. their greatest common divisor is $4\gcd(c_p,p+1)$;
4. $p$ is a good slope prime if and only if $\gcd(c_p,p+1)=1$; and an odd prime $\ell$ dividing both
   $c_p$ and $p+1$ satisfies $\ell\equiv1\pmod4$.

For example $c_{17}=-1$, so $17$ is a good slope prime.

**Proof sketch.** Since $p\equiv1\pmod8$, $2$ is a square, so some $r$ has $r^2=2$, and
$d=75-53r$, $\bar d=75+53r$ satisfy $d\bar d=7$; by quadratic reciprocity
$\chi(7)=(p/7)=-1$, so $d$ and $\bar d$ are nonzero and $\chi(d)\chi(\bar d)=-1$.
By scaling, $\varphi_p(-d^2)=\chi(d)\varphi_p(-1)$ and
$\varphi_p(-1)=\chi(i)\varphi_p(1)=\varphi_p(1)$ for $i^2=-1$, since $i$ is a square when $p\equiv1\pmod8$; with the point count formula this gives (2). Four divides both point counts, and
$p+1\equiv2\pmod 8$, so $c_p$ is odd; Jacobsthal's identity gives $p=c_p^2+e_p^2$. For $c$ odd and
$n\equiv2\pmod4$, $\gcd(n-2c,n+2c)=4\gcd(c,n)$, which is (3), and (4) follows from the definition
of a good slope prime. If an odd $\ell$ divides $c_p$ and $p+1$, then $e_p^2=p-c_p^2\equiv-1\pmod\ell$,
so $\ell\equiv1\pmod 4$.

## Depends on

- [The two-slope prime pattern](../main/two-slope-pattern.md)
- [Character sums for the curves $y^2=x^3+ax$](character-sums.md)

## Proof depends on

- [Jacobsthal's identity](jacobsthal.md)
- [Four divides the point count of $y^2=x^3-D^2x$](four-divides-point-count.md)

## Sources

- [The description of good primes](../../sources/density-locators.md#the-description-of-good-primes)
