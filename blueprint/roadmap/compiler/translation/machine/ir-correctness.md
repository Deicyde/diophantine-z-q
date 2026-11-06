---
article_id: af_eb6a0733e131b143b2e19f9f
declaration: theorem
origin: cited
---

# The precision program computes the precision predicate

For every $\mathbf c\in\mathbb N^5$ the precision program $\mathcal R$ terminates on $\mathbf c$, and it
accepts $\mathbf c$ if and only if $\mathrm{accepts\_naturals}(\mathbf c)$. This includes every early
rejection, the origin and zero-ordinate cases and equal-abscissa additions, and uses no
property of $P_0$ other than its coordinates.

**Proof sketch.** *Representations.* The signed and quadratic-field macros compute the
operations of $\mathbb Z$ and $\mathbb Z[s]$ on normalized representatives; a field element is zero
iff its norm is zero, so every guarded division divides by a nonzero element. *Scalar
multiplication.* The binary loop keeps the invariant $\mathrm{acc}+[k]\,\mathrm{base}=[m]P_0$ (as
represented points), with $k$ halving at each iteration, so it terminates with $[m]P_0$; each
addition or doubling represents the group law by the Jacobian formulas, including the
exceptional branches. *Guards and values.* A triple with $Z\ne0$, $X\ne0$, $Y\ne0$ represents a
nondegenerate point and conversely, and $z=-x/y=-XZ/Y$; so steps 4-6 compute condition 2 and the
first test exactly. *Second test.* By capped arithmetic, $\beta=\sigma_L(B)$ with
$B=A^{(0)}_{\rm ht}|\kappa F(n)|^{24}$, the precision loop accepts iff $4^\beta\le L$, which is
$\sigma_L(4^{\sigma_LB})\le L$, i.e. $4\epsilon_l<4^{-B}$. The case $L=0$ (when $V-1<4U$) is
included: the remainder starts at $0$, the program rejects, and $4\epsilon_l<4^{-B}$ fails
since it would need $4^B\le0$. Termination: every loop decreases a
natural counter, and all other steps are straight-line. Steps 1-2 implement condition 1.

## Depends on

- [The precision program](precision-ir.md)
- [The precision predicate](precision-predicate.md)

## Proof depends on

- [Norm zero implies zero](quadratic-norm-zero.md)
- [Jacobian formulas for the group law](jacobian-formulas.md)
- [The fixed Jacobian triple of the generator](projective-generator.md)
- [Capped arithmetic](capped-arithmetic.md)

## Sources

- [Section 10.3 precision IR](../../../../sources/compiler-translation-locators.md#section-103-precision-ir)
- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
