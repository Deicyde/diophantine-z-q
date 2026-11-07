---
article_id: af_81092045b02e5b696f16c4c3
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.l1, ZInQ.Size.PairRing, ZInQ.Size.pairNorm, ZInQ.Size.pairDeg
---

# Coefficient norms and degrees

For a polynomial $f=\sum_\alpha c_\alpha X^\alpha\in\mathbb Z[X_i:i\in I]$ (finitely many nonzero
$c_\alpha$), its coefficient $\ell^1$ norm is
$$\|f\|_1=\sum_\alpha|c_\alpha|\in\mathbb N,$$
and $\deg f$ is its total degree ($\deg0=0$).

Let $S=\mathbb Z[X_i:i\in I]$ and $S[s]=S[t]/(t^2-2)$, whose elements are pairs $(a,b)$, written
$a+bs$, with $(a,b)+(c,d)=(a+c,b+d)$ and $(a,b)(c,d)=(ac+2bd,\ ad+bc)$. The weighted pair norm
and degree are
$$\|a+bs\|=\|a\|_1+2\|b\|_1,\qquad\deg(a+bs)=\max(\deg a,\deg b).$$

This is a definition.

## Depends on

None.

## Sources

- [Section 12.1 norms and division polynomials](../../../sources/size-locators.md#section-121-norms-and-division-polynomials)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
