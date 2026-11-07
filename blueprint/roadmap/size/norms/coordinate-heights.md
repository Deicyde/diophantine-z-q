---
article_id: af_8e91cd3347a520216f16e82e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.iota_coord_height
---

# Heights of the codes in the guard box

Let $T\ge0$ be an integer and $K=2^{30}(T+1)^3$. For every integer $n$ with $|n|\le T$,
each of the five coordinates of $\iota(n)$ is a rational number whose reduced numerator has
absolute value at most $2^K$ and whose positive reduced denominator is at most $2^K$.

**Proof sketch.** For $n=0$, $\iota(0)=(1,0,0,0,0)$. Let $1\le|n|\le T$. By the fixed point codes
(which use that $P_0$ has infinite order and the multiplication-by-$n$ formulas), for $n\ge1$,
$\psi_n(P_0)\ne0$ and
$$x([n]P_0)=x(P_0)-\frac{\psi_{n+1}(P_0)\psi_{n-1}(P_0)}{\psi_n(P_0)^2},\qquad
y([n]P_0)=\frac{\psi_{2n}(P_0)}{2\psi_n(P_0)^4},$$
and $\iota(-n)$ differs from $\iota(n)$ only in the signs of the ordinate coordinates.

*Values of $\psi_m(P_0)$.* The coordinates of $P_0$ over the denominator $32$ are
$x_0=6564/32$, $x_1=-4640/32$, $y_0=-123720/32$, $y_1=87483/32$, with numerators below
$2^{17}$ in absolute value. For $|m|\le2T$ put $\delta=2(|m|+1)^3\ge\deg\Psi_{m,c}$. Then
$c_m=32^\delta$, $a_m=32^\delta\Psi_{m,0}(P_0)$ and $b_m=32^\delta\Psi_{m,1}(P_0)$ are integers with
$\psi_m(P_0)=(a_m+b_ms)/c_m$, and each monomial of $\Psi_{m,c}$ contributes at most $2^{17\delta}$
after clearing, so $|a_m|,|b_m|\le\|\Psi_{m,c}\|_1\,2^{17\delta}\le2^{135(|m|+1)^3}$ and
$c_m=2^{10(|m|+1)^3}$. With $(|m|+1)^3\le(2T+1)^3\le8(T+1)^3$ all these triples, and the triple
$(1641,-1160,8)$ of $x(P_0)$, have size at most $H_0=2^{1280(T+1)^3}$.

*Field operations.* $x([n]P_0)$ and $y([n]P_0)$ are obtained from these values by at most
eight successive levels of additions, subtractions, products, doubling and quotients
(in fact four: $\psi_n^2$ and $\psi_{n+1}\psi_{n-1}$, their quotient, the difference with
$x(P_0)$; and $\psi_n^4$, $2\psi_n^4$, the quotient). Each level takes a size bound $H$ to $3H^4$.
With $h_k=\log_2H_k$, $h_{k+1}\le4h_k+2$, so $h_8\le4^8(h_0+1)\le65536\,(1280(T+1)^3+1)<2^{27}(T+1)^3\le K$.
By the component part of the size lemma, the four rational coordinates of $[n]P_0$ have reduced
numerators and denominators at most $2^K$; the first code coordinate is $0$.

## Depends on

- [Point codes](../../model/point-codes.md)

## Proof depends on

- [Closed numerical comparisons](../constants/closed-comparisons.md)
- [Fixed point codes by division polynomials](../../model/field/fixed-point-codes.md)
- [The point $P_0$](../../model/field/generator-point.md)
- [Size of the division polynomials](division-polynomial-size.md)
- [Sizes under quadratic-field operations](quadratic-heights.md)

## Sources

- [Section 12.1 constructor bounds](../../../sources/size-locators.md#section-121-constructor-bounds)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
