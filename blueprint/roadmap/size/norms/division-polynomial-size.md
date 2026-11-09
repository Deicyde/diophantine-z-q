---
article_id: af_e412ee299926ce7f7164d234
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.normDiv_size, ZInQ.Size.psiComponent_size
---

# Size of the division polynomials

Work in $S[s]$ with $S=\mathbb Z[x_0,x_1,y_0,y_1]$, put $x=x_0+x_1s$, $y=y_0+y_1s$ and
$A=-11243+7950s$, and let $F_n=f_n(x)\in S[s]$ for the normalized division polynomials $f_n$ of
$y^2=x^3+Ax$. Then for every $n\ge0$
$$\deg F_n\le(n+1)^3,\qquad\|F_n\|\le2^{100(n+1)^3}.$$
Consequently, for every $n\in\mathbb Z$ and $c\in\{0,1\}$, the component polynomial
$\Psi_{n,c}\in S$ (the coefficient of $s^c$ in $\psi_n(x,y)$) satisfies
$$\deg\Psi_{n,c}\le2(|n|+1)^3,\qquad\|\Psi_{n,c}\|_1\le2^{101(|n|+1)^3}.$$

**Proof sketch.** Norms: $\|x\|=\|y\|=3$, $\|A\|=11243+2\cdot7950=27143<2^{15}$, and
$D_0=16(x^3+Ax)^2$ has degree $6$ and $\|D_0\|\le16(27+3\cdot27143)^2<2^{38}$.

*Base cases.* $F_0=0$, $F_1=F_2=1$. $F_3=3x^4+6Ax^2-A^2$ has degree at most $4\le64$ and norm
at most $3\cdot3^4+6\cdot27143\cdot3^2+27143^2<2^{30}$. $F_4=2(x^6+5Ax^4-5A^2x^2-A^3)$ has degree at most
$6\le125$ and norm at most $2(3^6+5\cdot27143\cdot3^4+5\cdot27143^2\cdot3^2+27143^3)<2^{46}$.

*Even step*, $n=2m$, $m\ge3$: $F_{2m}=F_m(F_{m+2}F_{m-1}^2-F_{m-2}F_{m+1}^2)$, all indices below
$2m$. By induction the first product has exponent sum $(m+1)^3+(m+3)^3+2m^3=4m^3+12m^2+30m+28$
(including the factor $F_m$), the second $(m+1)^3+(m-1)^3+2(m+2)^3=4m^3+12m^2+30m+16$, smaller.
Since $(2m+1)^3-(4m^3+12m^2+30m+28)=4m^3-24m-27\ge9$ for $m\ge3$, the degree is at most
$(2m+1)^3-9$ and $\log_2\|F_{2m}\|\le100((2m+1)^3-9)+1<100(2m+1)^3$ (the $+1$ for the
difference of two terms).

*Odd step*, $n=2m+1$, $m\ge2$: $F_{2m+1}=D_0L-R_m$ ($m$ even) or $L-D_0R_m$ ($m$ odd) with
$L=F_{m+2}F_m^3$ and $R_m=F_{m-1}F_{m+1}^3$, all indices below $2m+1$. The exponent sums are
$(m+3)^3+3(m+1)^3$ and $m^3+3(m+2)^3$, whose differences from $(2m+2)^3$ are
$4m^3+6m^2-12m-22\ge10$ and $4m^3+6m^2-12m-16\ge16$ for $m\ge2$. The factor $D_0$ costs at most
$6$ in degree and $38$ in $\log_2$ of the norm, the difference one more bit, and
$6\le10$, $38+1\le1000$.

*Components.* For odd $n\ge0$, $\psi_n=F_n$; for even $n\ge0$, $\psi_n=2yF_n$ with
$\|2y\|=6<2^3$ and degree one more; and $\psi_{-n}=-\psi_n$. So $\deg\psi_n\le(|n|+1)^3+1\le2(|n|+1)^3$
and $\|\psi_n\|\le2^{100(|n|+1)^3+3}\le2^{101(|n|+1)^3}$ for $n\ne0$ ($\psi_0=0$). Each component
has $\ell^1$ norm and degree at most those of the pair.

These polynomials are never expanded at the astronomical indices; the bound is proved by
strong induction on $n$ from the recurrences.

## Depends on

- [Normalized division polynomials and their components](../../syntax/division-polynomials.md)
- [Coefficient norms and degrees](l1-norm.md)

## Proof depends on

- [Closed numerical comparisons](../constants/closed-comparisons.md)
- [The weighted pair norm](pair-norm.md)

## Sources

- [Section 12.1 norms and division polynomials](../../../sources/size-locators.md#section-121-norms-and-division-polynomials)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
