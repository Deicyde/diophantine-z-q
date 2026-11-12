---
article_id: af_b2390a628b3dabdf837a7887
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.JHeight.abs_monomial_le, ZInQ.JHeight.lower_bound
---

# A lower bound for the larger of $57600F_h^2$ and $G_h^6$

Let $F_h$ and $G_h$ be the binary forms of the Hauptmodul value. If $a,b,m$ are integers with
$|a|\le m$ and $|b|\le m$, then $|a^ib^j|\le m^{i+j}$ for all natural numbers $i,j$. Let $a,b,m$
be integers with
$|a|\le m$, $|b|\le m$, $m>0$, and $m=|a|$ or $m=|b|$. Then
$$m^{12}\le10^{48}\max\bigl(57600F_h(a,b)^2,\ G_h(a,b)^6\bigr).$$

**Proof sketch.** Suppose not. Then $57600\cdot10^{48}F_h^2<m^{12}$ and $10^{48}G_h^6<m^{12}$,
so taking square and sixth roots, $240\cdot10^{24}|F_h|<m^6$ and $10^8|G_h|<m^2$; hence
$240\cdot10^{24}\,m|F_h|<m^7$ and $10^8\,m^5|G_h|<m^7$. Since $|a^ib^j|\le m^{i+j}$, each
cofactor in the two identities of the cancellation bound is at most the sum of the absolute values
of its coefficients times the matching power of $m$.

If $m=|a|$, the first identity and the triangle inequality give
$$3m^7\le5000\,m|F_h|+20328129\,m^5|G_h|<\Bigl(\frac{5000}{240\cdot10^{24}}+\frac{20328129}{10^8}\Bigr)m^7<3m^7,$$
a contradiction. If $m=|b|$, the second identity gives
$$104976000000\,m^7\le38651\,m|F_h|+184009200\,m^5|G_h|<\Bigl(\frac{38651}{240\cdot10^{24}}+\frac{184009200}{10^8}\Bigr)m^7,$$
again a contradiction.

## Depends on

- [The Hauptmodul value $J(u)$](hauptmodul-value.md)

## Proof depends on

- [The cancellation in $J(u)$ is bounded](cancellation-bound.md)

## Sources

- [Step F4](../../../sources/height-locators.md#step-f4)
