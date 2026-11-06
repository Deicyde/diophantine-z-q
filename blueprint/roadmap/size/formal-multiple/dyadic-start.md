---
article_id: af_a99666b6573a75b87d245b1d
declaration: lemma
origin: cited
---

# $P_0$ at the dyadic place

At the prime $(s)$ of $\mathbb Z[s]$, normalized by $v_s(s)=1$ (so $v_s(2)=2$),
$$v_s\bigl(x(P_0)\bigr)=-6,\qquad v_s\bigl(y(P_0)\bigr)=-9 .$$
Hence $P_0$ lies in the filtration subgroup $W_3$ of $E$ at $(s)$.

This is a finite computation: $x(P_0)=\frac{1641}{8}-145s$ and
$y(P_0)=-\frac{15465}{4}+\frac{87483}{32}s$ with $v_2(1641/8)=-3$, $v_2(145)=0$,
$v_2(15465/4)=-2$, $v_2(87483/32)=-5$.

**Proof sketch.** By the valuation formula $v_s(c_0+c_1s)=\min(2v_2(c_0),2v_2(c_1)+1)$:
$v_s(x(P_0))=\min(-6,1)=-6$ and $v_s(y(P_0))=\min(-4,-9)=-9$. So $v_s(x)=-2\cdot3$, and $P_0\in W_3$.

## Depends on

- [The point $P_0$](../../model/field/generator-point.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)
- [The filtration by abscissa valuation](filtration.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
