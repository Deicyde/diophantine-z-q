---
article_id: af_47ec48ac7deb1d7793a0ecd7
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Mult.SlopeRepresentation, ZInQ.Mult.GoodSlope
---

# The slope representation

For a real $B_0$, say that $t\in\mathbb Q$ satisfies *conditions 1-4 for $B_0$* if:

1. $t\notin\mathcal C\cup\{1\}$;
2. for every $p\in S_b$: $|v_p(t-1)|\le B_p$ and $|v_p(F(t)/(t-1)^8)|\le8B_p$;
3. every odd contact prime $p\notin S_b$ of $t$ satisfies $p>B_0$, is a good slope prime (there is
   $r\in\mathbb Z/p$ with $r^2=2$ and $75\mp53r\ne0$ such that the point counts $d_1,d_2$ of
   $y^2=x^3-(75\mp53r)^2x$ over $\mathbb Z/p$ satisfy $\gcd(d_1,d_2)=4$; for odd $p$: $p$ splits
   in $K_0$ and both reductions of $E$ above $p$ are good with orders of gcd $4$), and
   $v_p(t-c)=1$ for every $c\in\mathcal C$ with $v_p(t-c)>0$;
4. $t$ has at most six odd contact primes outside $S_b$.

A *good slope* is a $t$ satisfying conditions 1-4 for $B_0=0$; as primes are positive, these
are the conditions for any $B_0\le0$, and the conditions for any $B_0$ imply them.

The slope representation is the assertion that every integer $A$ is a sum $t_1+t_2+t_3=A$ of
three good slopes.

These are the conditions of the slopes from the prime pattern. The slope representation is
all that the completeness of the multiplication template uses of a prime pattern; both the
twenty-two-prime pattern and the two-slope pattern give it.

## Depends on

- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)

## Sources

- [Prime pattern](../../../sources/multiplication-locators.md#prime-pattern)
- [Choice of shifts](../../../sources/multiplication-locators.md#choice-of-shifts)
