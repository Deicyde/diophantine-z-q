---
article_id: af_889d4242784987bdf424039d
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.pattern_slopes
---

# Slopes of an integer from the prime pattern

Assume the twenty-two-prime pattern. For every $A\in\mathbb Z$ and every real $B_0$ there are
$t_1,t_2,t_3\in\mathbb Q$ with $t_1+t_2+t_3=A$ such that each $t=t_j$ satisfies:

1. $t\notin\mathcal C\cup\{1\}$;
2. for every $p\in S_b$: $|v_p(t-1)|\le B_p$ and $|v_p(F(t)/(t-1)^8)|\le8B_p$, in particular
   both are at most $C_p=14B_p$;
3. every odd contact prime $p\notin S_b$ of $t$ satisfies $p>B_0$, is a good slope prime
   (it splits in $K_0$, both reductions of $E$ above it are good, and their orders $d_1,d_2$
   satisfy $\gcd(d_1,d_2)=4$; the good primes of the
   [pattern hypothesis](../../main/prime-pattern.md) satisfy moreover $p\nmid d_1d_2$, which
   is not needed here), and has $v_p(t-c)=1$ for every $c\in\mathcal C$ with
   $v_p(t-c)>0$ (there is only one such $c$, because $p>324$ divides no difference of two
   elements of $\mathcal C$);
4. $t$ has at most six odd contact primes outside $S_b$.

This is the application of Proposition 6.2 to one of the nine integral homogeneous
quantities of a true triple; the selected prime values need not be distinct.

**Proof sketch.** Apply the pattern with $A$ and $B_0'=\max(B_0,H_{\max})$: there are
integers $u_1,u_2,v$, $v\ne0$, with $u_3=Av-u_1-u_2$, such that $v$ and every $u_j-bv$
($b\in\mathcal C\cup\{1\}$) equal $\epsilon kp$ with $\epsilon=\pm1$, $k=dh'$ ($d\mid P_s^4$,
$h'\in\mathcal H$) and $p>B_0'$ a good pattern prime. Put $t_j=u_j/v$; then $\sum_jt_j=A$ and
$t_j-b=(u_j-bv)/v\ne0$, which is (1). For $q\in S_b$, $q\ne p$ because $p>H_{\max}$, and
$v_q(k)\le B_q$: if $q\le324$, $v_q(d)\le4$ and $q\nmid h'$; if $q\in\mathcal H$, $q\nmid d$ and
$v_q(h')\le1$. So every pattern value has $q$-adic valuation in $[0,B_q]$, and
$t-1=(u_j-v)/v$, $F(t)/(t-1)^8=v^2\prod_{c\in\mathcal C}(u_j-cv)/(u_j-v)^8$ give (2). For a prime
$q\notin S_b$ with $v_q(t_j-c)>0$, $q$ divides $u_j-cv=\epsilon kp$ and not $k$, so $q=p$ is the
prime of that value; hence at most one such prime for each of the six $c$, which is (4).
Moreover $v_q(u_j-cv)=1$ and $v_q(v)\in\{0,1\}$, so $v_q(t_j-c)>0$ forces $v_q(t_j-c)=1$;
and $q=p>B_0'\ge B_0$ is a good pattern prime, hence a good slope prime, which is (3).

## Depends on

- [Prime sets and clearing exponents of the multiplication certificate](../certificate/constants.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [Properties of the multiplication constants](../certificate/constants-properties.md)

## Sources

- [Prime pattern](../../../sources/multiplication-locators.md#prime-pattern)
- [Choice of shifts](../../../sources/multiplication-locators.md#choice-of-shifts)
- [Fixed local clearing](../../../sources/multiplication-locators.md#fixed-local-clearing)
