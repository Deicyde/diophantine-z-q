---
article_id: af_b8092773875eeb5756c0c77a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.JHeight.heightH6_eq, ZInQ.JHeight.sixContactMin_of_jHeightBound
---

# The $j$-form implies the minimal height hypothesis

Let $\mathcal C$, $h$ and $X(R)=\max(1,C_{\rm cm},Q_R^{17})$ be as in the $j$-form of the height
hypothesis. For every real $R$, $H_6(S;R)=2\cdot10^{13}X(R)$ for every $S$, by the definition of
$H_6(S;R)$ in the six-contact estimate (it does not depend on $S$); write $H_6(R)$ for it. If the
$j$-form holds at
$S=S_{\rm mul}$, then the minimal height hypothesis holds: for every $u\in\mathbb Q\setminus\mathcal C$,
$$h(u)\le H_6(D)\,M_{S_{\rm mul}}(u)^{24}.$$

**Proof sketch.** Let $u\notin\mathcal C$, write $M=M_{S_{\rm mul}}(u)$ and
$K=40\cdot10^4\cdot2^{24}+22$. From the height of $J(u)$ to the height of $u$,
$12h(u)\le h(J(u))+450$, and the $j$-form gives $h(J(u))\le K\,X(D)\,M^{24}$. Here $X(D)\ge1$, and
$M\ge1$ because it is a product of primes, so $Y=X(D)M^{24}\ge1$. Then
$$h(u)\le\frac{KY+450}{12}\le2\cdot10^{13}\,Y=H_6(D)\,M^{24},$$
since $K+450<2.4\cdot10^{14}$ and $Y\ge1$.

## Depends on

- [The $j$-form of the height hypothesis](j-height-bound.md)
- [The minimal height hypothesis](../six-contact-min.md)
- [The six-contact height estimate](../six-contact-estimate.md)

## Proof depends on

- [From the height of $J(u)$ to the height of $u$](height-of-u-from-j.md)

## Sources

- [The $j$-form of H](../../../sources/height-locators.md#the-j-form-of-h)
- [Step F4](../../../sources/height-locators.md#step-f4)
- [Theorem 4.1](../../../sources/manuscript.md#theorem-41)
