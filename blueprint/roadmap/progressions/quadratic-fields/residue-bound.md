---
article_id: af_931dc516fbf1a47b26d3762d
declaration: theorem
origin: background
---

# A lower bound for the residue of $\zeta_K$

Let $d$ be a squarefree integer with $d\ne1$, $K=\mathbb Q(\sqrt d)$, and let
$$\kappa_K=\frac{2^{r_1}(2\pi)^{r_2}h_KR_K}{w_K\sqrt{|D_K|}}$$
be the residue at $s=1$ of the Dedekind zeta function $\zeta_K(s)$ (the class number
formula), where $h_K$ is the class number, $R_K$ the regulator, $w_K$ the number of roots of
unity and $D_K$ the discriminant. Then
$$\kappa_K\ge\frac{\log\frac{1+\sqrt5}{2}}{6\sqrt{|d|}} .$$

**Proof sketch.** Use $h_K\ge1$, $w_K\le6$ and $\sqrt{|D_K|}\le2\sqrt{|d|}$. If $d<0$, then
$r_1=0$, $r_2=1$ and $R_K=1$, so $\kappa_K\ge2\pi/(6\cdot2\sqrt{|d|})=\pi/(6\sqrt{|d|})$,
and $\pi>\log\frac{1+\sqrt5}2$. If $d>1$, then $r_1=2$, $r_2=0$ and
$R_K\ge\log\frac{1+\sqrt5}2$, so $\kappa_K\ge4\log\frac{1+\sqrt5}2/(6\cdot2\sqrt d)$, which is
at least the claimed bound.

## Depends on

- [The quadratic field $\mathbb Q(\sqrt d)$](quadratic-field.md)

## Proof depends on

- [The discriminant of $\mathbb Q(\sqrt d)$](discriminant-bound.md)
- [The signature of $\mathbb Q(\sqrt d)$](signature.md)
- [Roots of unity in a quadratic field](roots-of-unity.md)
- [The regulator of an imaginary quadratic field](imaginary-regulator.md)
- [The regulator of a real quadratic field](real-regulator.md)

## Sources

- [Marcus, Chapter 7](../../../sources/progressions-locators.md#marcus-chapter-7)
- [Davenport, Chapter 6](../../../sources/progressions-locators.md#davenport-chapter-6)
