---
article_id: af_fd209209c92cd80b7dcf1b3c
declaration: lemma
origin: bridged
---

# The generator lies in the dyadic formal group

Let $v_s$ be the valuation of $K_0$ at the prime $(s)$, normalized by $v_s(s)=1$ (so
$v_s(2)=2$). Then
$$v_s\bigl(x(P_0)\bigr)=-6,\qquad v_s\bigl(y(P_0)\bigr)=-9,\qquad v_s\bigl(z(P_0)\bigr)=3 .$$
Hence, in the completion $K_{(s)}$, $P_0\in E_3(K_{(s)})\subset E_1(K_{(s)})$, and every
multiple $[n]P_0$ ($n\in\mathbb Z$) lies in $E_1(K_{(s)})$ with $v_s(z([n]P_0))\ge3$.

The numerical input is a finite computation: $1641$ and $87483$ are odd, $8=2^3$ and
$32=2^5$.

**Proof sketch.** $x(P_0)=(1641-1160s)/8$. By the valuation formula at $(s)$,
$v_s(1641-1160s)=\min(2v_2(1641),2v_2(1160)+1)=\min(0,7)=0$ and $v_s(8)=6$. Similarly
$y(P_0)=(-123720+87483s)/32$ with $v_s(-123720+87483s)=\min(2\cdot3,0+1)=1$ and
$v_s(32)=10$, so $v_s(y)=-9$. Then $v_s(z)=v_s(x)-v_s(y)=3$. The statements about multiples
follow from the subgroup property of $E_3$ and from
$v_s(z([n]P))\ge v_s(z(P))$ in the formal group.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The formal group of $y^2=x^3+Ax$](formal-group.md)

## Proof depends on

- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Least formal multiple exists](../../../sources/multiplication-locators.md#least-formal-multiple-exists)
