---
article_id: af_279f3262ccc49955160fc21e
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.TwoSlopePattern, ZInQ.GoodSlopePrime
---

# The two-slope prime pattern

Let $\mathcal C=\{0,-15,-20,-24,-30,-60\}$, let $\mathcal H$ be the prime catalogue of the
twenty-two-prime pattern (the first twenty-two primes greater than $324$ in each unit residue
class modulo $W=4P_s$), and $E:y^2=x^3-(75-53\sqrt2)^2x$. Call a prime $p$ a *good slope
prime* if there is $r\in\mathbb Z/p$ with $r^2=2$, $75-53r\ne0$ and $75+53r\ne0$ in
$\mathbb Z/p$, and the numbers $d_1,d_2$ of points, the point at infinity included, of
$y^2=x^3-(75-53r)^2x$ and $y^2=x^3-(75+53r)^2x$ over $\mathbb Z/p$ satisfy $\gcd(d_1,d_2)=4$.
For odd $p$ this says that $p$ splits in $\mathbb Q(\sqrt2)$, that both reductions of $E$ at
the places above $p$ are good, and that their orders satisfy $\gcd(d_1,d_2)=4$: the good
primes of the twenty-two-prime pattern without the condition $p\nmid d_1d_2$.

The two-slope pattern is the assertion that for every $A\in\mathbb Z$ there are integers $u,v$
with $v\ne0$ such that

1. for each $c\in\mathcal C$, the absolute values of the twelve numbers $u-cv$ and
   $u-(A+10-c)v$ are good slope primes greater than $324$ and outside $\mathcal H$;
2. each of $v$, $u-v$ and $u-(A+9)v$ has $q$-adic valuation at most $4$ at every prime
   $q\le324$ and at most $1$ at every $q\in\mathcal H$.

(The three numbers in 2 are nonzero: $u=v$ would make $u+15v=16v$ prime, and
$u=(A+9)v$ would make $u-(A+25)v=-16v$ prime.) In other words, a homothetic copy
$u-v\cdot(\mathcal C\cup(A+10-\mathcal C))$ of a twelve-point set lies in the good slope primes,
with the common difference $v$ and the numerators of $t-1$ controlled at the old primes. The
proof uses it through the three slopes $u/v$, $A+10-u/v$ and $-10$, which sum to $A$.

This is a different linear pattern in primes from the twenty-two-prime pattern, not a
consequence of it. Its expected proof is the argument of Proposition 6.2 with two variables
and twelve linear forms: the Green–Tao–Ziegler theory of linear equations in primes (the
Green–Tao asymptotic, the Möbius–nilsequences theorem and the inverse theorem for the Gowers
norms), as for the twenty-two-prime pattern. It is not proved here; the main theorem holds
with it in place of the twenty-two-prime pattern.

## Depends on

None.

## Sources

- [Proposition 6.2](../../sources/manuscript.md#proposition-62)
