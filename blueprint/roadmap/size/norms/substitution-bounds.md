---
article_id: af_9158651be635a1bdd958d850
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.substitution_bounds, ZInQ.Size.rename_bounds, ZInQ.Size.l1_rename_eq
---

# Substitution and renaming bounds

Let $P\in\mathbb Z[X_i:i\in I]$ and $Q_i\in\mathbb Z[Y_j:j\in J]$ for $i\in I$, and let
$P(Q)$ be the image of $P$ under the ring homomorphism $X_i\mapsto Q_i$. If $d\ge1$ and $M\ge1$
satisfy $\deg Q_i\le d$ and $\|Q_i\|_1\le M$ for every $i$ such that $X_i$ occurs in $P$, then
$$\deg P(Q)\le d\cdot\deg P,\qquad\|P(Q)\|_1\le\|P\|_1\,M^{\deg P}.$$
In the manuscript's notation, $\deg P(Q)\le\deg P\cdot\max(1,\max_i\deg Q_i)$ and
$\|P(Q)\|_1\le\|P\|_1\max(1,\max_i\|Q_i\|_1)^{\deg P}$.

For a renaming $Q_i=Y_{\sigma(i)}$ with any map $\sigma:I\to J$ (not necessarily injective),
$$\deg P(Y_\sigma)\le\deg P,\qquad
\|P(Y_\sigma)\|_1=\sum_\beta\Bigl|\sum_{\alpha\mapsto\beta}c_\alpha\Bigr|\le\sum_\alpha|c_\alpha|=\|P\|_1 .$$

**Proof sketch.** Write $P=\sum_\alpha c_\alpha X^\alpha$. Then
$P(Q)=\sum_\alpha c_\alpha\prod_iQ_i^{\alpha_i}$; by the elementary estimates each monomial
image has degree at most $\sum_i\alpha_i\deg Q_i\le d|\alpha|\le d\deg P$ and norm at most
$\prod_i\|Q_i\|_1^{\alpha_i}\le M^{|\alpha|}\le M^{\deg P}$ (as $M\ge1$); sum over $\alpha$. For a
renaming each monomial $X^\alpha$ maps to a single monomial of the same degree, and
coefficients of monomials with the same image add, which can only decrease the $\ell^1$
norm.

## Depends on

- [Coefficient norms and degrees](l1-norm.md)

## Proof depends on

- [Elementary estimates for the coefficient norm](l1-norm-estimates.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
