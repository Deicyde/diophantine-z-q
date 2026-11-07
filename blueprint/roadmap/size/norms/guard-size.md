---
article_id: af_e749e0a0a9f07c74c2982ab0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.guardPoly_size
---

# Size of the guard polynomial

For every integer $T\ge0$, the false-triple product $G_T\in\mathbb Z[X_1,\dots,X_{15}]$ satisfies
$$\deg G_T\le16(T+1)^3,\qquad\|G_T\|_1\le2^{2^{39}(T+1)^6}.$$

**Proof sketch.** $G_T$ is a product of at most $(2T+1)^3\le8(T+1)^3$ factors, one for each
false triple $(a,b,c)\in[-T,T]^3$. Fix one, with coordinates $A_j/B_j$ of
$(\iota(a),\iota(b),\iota(c))$ and $D=\prod_{j=1}^{15}B_j$. With $K=2^{30}(T+1)^3$ the heights of
the codes give $|A_j|,B_j\le2^K$, so $D\le2^{15K}$ and $|(D/B_j)A_j|\le2^{15K}$. Each
$(DX_j-(D/B_j)A_j)^2$ has degree $2$ and norm at most $(2\cdot2^{15K})^2=2^{30K+2}$, so the factor
$\sum_{j=1}^{15}(DX_j-(D/B_j)A_j)^2$ has degree at most $2$ and norm at most
$15\cdot2^{30K+2}<2^{30K+6}$. Multiplying: $\deg G_T\le2\cdot8(T+1)^3$ and
$\log_2\|G_T\|_1\le8(T+1)^3(30K+6)\le8\cdot31\cdot2^{30}(T+1)^6<2^{39}(T+1)^6$. The empty product
($T=0$, where there is no false triple) is $1$.

The polynomial is never expanded; the bound uses only the product structure.

## Depends on

- [The finite false-triple product](../../syntax/constants/guard-product.md)
- [Coefficient norms and degrees](l1-norm.md)

## Proof depends on

- [Heights of the codes in the guard box](coordinate-heights.md)
- [Elementary estimates for the coefficient norm](l1-norm-estimates.md)

## Sources

- [Section 12.1 constructor bounds](../../../sources/size-locators.md#section-121-constructor-bounds)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
