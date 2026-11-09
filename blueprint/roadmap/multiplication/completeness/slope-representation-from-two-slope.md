---
article_id: af_415f6e6a418ad5875f10c0b0
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.slopeRepresentation_of_twoSlopePattern
---

# The two-slope pattern gives the slope representation

Assume the two-slope pattern. Then the slope representation holds: every integer $A$ is the
sum of the three good slopes
$$\frac uv+\Bigl(A+10-\frac uv\Bigr)+(-10)=A,$$
with $u,v$ given by the pattern for $A$.

**Proof sketch.** The twelve numbers $u-cv$ and $u-(A+10-c)v$ ($c\in\mathcal C$) are, up to
sign, good slope primes greater than $324$ outside $\mathcal H$, hence outside $S_b$; and $v$,
$u-v$, $u-(A+9)v$ have valuation at most $B_q$ at every $q\in S_b$.

*The slope $t=u/v$.* Here $t-c=(u-cv)/v$. If $u=v$ then $u+15v=16v$ would be prime, so
$u-v\ne0$, and $t\notin\mathcal C\cup\{1\}$. At $q\in S_b$ every $u-cv$ is a $q$-adic unit, so
$v_q(t-1)=v_q(u-v)-v_q(v)$ and
$v_q(F(t)/(t-1)^8)=2v_q(v)-8v_q(u-v)$ lie in $[-B_q,B_q]$ and $[-8B_q,8B_q]$. An odd contact
prime $q\notin S_b$ of $t$ divides some $u-cv$, so it is the prime $|u-cv|$, a good slope
prime; then $v_q(u-c'v)\le1$ for all $c'$, and $v_q(t-c')>0$ forces $v_q(v)=0$ and
$v_q(t-c')=1$. There are at most six such primes, one for each $c$.

*The slope $A+10-u/v=u_2/v$*, with $u_2=(A+10)v-u$. Now $u_2-cv=-(u-(A+10-c)v)$ and
$u_2-v=-(u-(A+9)v)$, and the same argument applies with the other six primes.

*The slope $-10$.* Its contact values $-10-c$ are $-10,5,10,14,20,50$, whose prime factors are
at most $7$, so it has no odd contact prime outside $S_b$. Further $-10-1=-11$ and
$F(-10)=-7\cdot10^6=-2^6\cdot5^6\cdot7$, so at $q\le324$ the two valuations of condition 2 are
at most $1\le4$ and $13\le32$ in absolute value, and at $q\in\mathcal H$ they vanish.

## Depends on

- [The slope representation](slope-representation.md)
- [The two-slope prime pattern](../../main/two-slope-pattern.md)

## Proof depends on

- [Properties of the multiplication constants](../certificate/constants-properties.md)
