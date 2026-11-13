---
article_id: af_931dc516fbf1a47b26d3762d
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.dedekindZeta_residue_ge, ZInQ.Progressions.log_golden_pos, ZInQ.Progressions.log_golden_lt_one
---

# A lower bound for the residue of $\zeta_K$

Let $d$ be an integer that is not the square of a rational number, $K=\mathbb Q(\sqrt d)$, and
let
$$\kappa_K=\frac{2^{r_1}(2\pi)^{r_2}h_KR_K}{w_K\sqrt{|D_K|}}$$
be the residue at $s=1$ of the Dedekind zeta function $\zeta_K(s)$ (the class number
formula), where $h_K$ is the class number, $R_K$ the regulator, $w_K$ the number of roots of
unity and $D_K$ the discriminant. Then
$$\kappa_K\ge\frac{\log\frac{1+\sqrt5}{2}}{6\sqrt{|d|}} .$$

**Proof sketch.** Note $0<\log\frac{1+\sqrt5}2<1$. Use $h_K\ge1$, $w_K\le6$ and
$\sqrt{|D_K|}\le2\sqrt{|d|}$, so the denominator is at most $12\sqrt{|d|}$. If $d<0$, then
$r_1=0$, $r_2=1$ and $R_K=1$, so the numerator is at least $2\pi>2\log\frac{1+\sqrt5}2$ and
$\kappa_K\ge\pi/(6\sqrt{|d|})$. If $d>0$, then $r_1=2$, $r_2=0$ and
$R_K\ge\log\frac{1+\sqrt5}2$, so the numerator is at least $4\log\frac{1+\sqrt5}2$ and
$\kappa_K\ge\log\frac{1+\sqrt5}2/(3\sqrt d)$. Both are at least the claimed bound.

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
