---
article_id: af_f021dde0131533284aa1445c
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.canonHeight_R_pos, ZInQ.hx_lt_log_nine_of_multiple
---

# A multiple of a small point

1. $\widehat h(R)>0$; more precisely $8\widehat h(R)=2\widehat h([2]R)\ge\log41-\frac{\log392}{3}>0$.
2. If $R=[m]S+T$ with $S\in C(K_0)$, $T\in C(K_0)[2]$ and $m\in\mathbb Z$, $|m|\ge3$, then
   $$h_x(S)\le\frac{\log(41^3\cdot676)}{108}+\frac{\log392}{3}<\log9 .$$

**Proof sketch.** By the basic properties and the height of $2R$,
$2\widehat h([2]R)\ge h_x([2]R)-\frac{\log392}3=\log41-\frac{\log392}3$, positive by the comparison
$392<41^3$, and $\widehat h([2]R)=4\widehat h(R)$; this is (1). For (2),
$2\widehat h([2]R)\le h_x([2]R)+\frac{\log676}{3}=\log41+\frac{\log676}{3}$, so
$2\widehat h(R)\le\frac{3\log41+\log676}{12}=\frac{\log(41^3\cdot676)}{12}$. Since $T$ is two-torsion and
$\widehat h$ is quadratic, $\widehat h(R)=\widehat h([m]S)=m^2\widehat h(S)\ge9\widehat h(S)$, so
$2\widehat h(S)\le\frac{\log(41^3\cdot676)}{108}$. Then
$h_x(S)\le2\widehat h(S)+\frac{\log392}{3}$, and the final strict inequality is the comparison
$41^3\cdot676\cdot392^{36}<9^{108}$.

## Depends on

- [The canonical height on $C(K_0)$](canonical-height.md)
- [The certificate for the point $R$](../descent/point-r-certificate.md)

## Proof depends on

- [Basic properties of the canonical height](canonical-height-bounds.md)
- [The canonical height is quadratic](canonical-height-quadratic.md)
- [The height of $2R$](height-of-2r.md)
- [Two explicit integer comparisons](height-comparisons.md)

## Sources

- [Height comparison](../../../sources/model-locators.md#height-comparison)
