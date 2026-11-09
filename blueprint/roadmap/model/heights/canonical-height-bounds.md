---
article_id: af_95b3c0311d86c4ef2f72318f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.canonHeight_tendsto, ZInQ.two_canonHeight_le, ZInQ.hx_le_two_canonHeight, ZInQ.canonHeight_two_smul, ZInQ.canonHeight_add_twoTorsion
---

# Basic properties of the canonical height

For every $T\in C(K_0)$ the limit defining $\widehat h(T)$ exists, and:

1. $$2\widehat h(T)\le h_x(T)+\frac{\log676}{3}\qquad\text{and}\qquad
   h_x(T)\le2\widehat h(T)+\frac{\log392}{3};$$
2. $\widehat h([2]T)=4\widehat h(T)$;
3. $\widehat h(-T)=\widehat h(T)$, and $\widehat h(T+T')=\widehat h(T)$ for every $T'\in C(K_0)[2]$;
4. $\widehat h(T)\ge0$.

**Proof sketch.** Put $c_m=4^{-m}h_x([2^m]T)$. The duplication height bounds give
$-4^{-m-1}\log392\le c_{m+1}-c_m\le4^{-m-1}\log676$, so $(c_m)$ is Cauchy, and summing the
geometric series from $m=0$ gives $-\frac{\log392}3\le\lim c_m-h_x(T)\le\frac{\log676}3$, which is
(1). (2) is a shift of the index. (3): $x(-P)=x(P)$ and $[2^m](-T)=-[2^m]T$; and
$[2](T+T')=[2]T$, so by (2) $\widehat h(T+T')=\widehat h([2]T)/4=\widehat h(T)$. (4) holds since
$h_x\ge0$.

## Depends on

- [The canonical height on $C(K_0)$](canonical-height.md)

## Proof depends on

- [Height bounds for doubling on $C$](duplication-height-bounds.md)
- [The height of a fraction in $\mathbb Z[\sqrt2]$](x-height-formula.md)

## Sources

- [Height comparison](../../../sources/model-locators.md#height-comparison)
